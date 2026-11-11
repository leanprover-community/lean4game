import type { ChildProcessWithoutNullStreams } from 'node:child_process'
import { randomUUID } from 'node:crypto'

import { createLspClient, type LspClient } from './lspClient.js'
import { forgetInstanceDocs } from './openDocuments.js'
import { noBwrap, spawnGame } from './sandbox.js'

export interface LeanInstance {
  id: string
  gamePath: string
  /** where the `gamePath` is mounted inside the bubblewrap containter. */
  gamePathBwrap: string
  process: ChildProcessWithoutNullStreams
  status: LeanInstanceStatus
  startedAt: Date
  exitCode: number | null
  client: LspClient
  /** resolves once the LSP `initialize`/`initialized` handshake has completed */
  lspReady: Promise<void>
  /** the game as requested by the player, lower case, for the play statistics */
  game: { owner: string; repo: string }
  /** time in ms of the last start, check or keepalive, instances idle for too long are stopped */
  lastActivityAt: number
  /** time in ms when the process exited */
  exitedAt?: number
  /** time of the last check in ms, for the play statistics */
  lastCheckAt?: number
}

export type LeanInstanceStatus = 'starting' | 'running' | 'exited'

const instances = new Map<string, LeanInstance>()

/** Instances without a check or keepalive for this long are stopped */
const IDLE_MS = (Number(process.env.LEAN_IDLE_MINUTES) || 5) * 60_000
const CLEANUP_INTERVAL_MS = 30_000

export function startInstance(
  gamePath: string,
  /** the game as requested by the player, lower case, for the play statistics */
  game: { owner: string; repo: string },
  /** The GameSkeleton doesn't have its own copy of the server and needs leangame as a local dependency */
  includeServerCopy?: boolean,
): LeanInstance {
  const child = spawnGame(gamePath, ['lake', 'serve', '--'], includeServerCopy)

  const client = createLspClient(child)

  const handshake = client
    .request('initialize', {
      processId: process.pid,
      rootUri: null,
      capabilities: {},
    })
    .then(() => client.notify('initialized', {}))
    .then(() => undefined)
  // the `initialize` request never settles if the process dies, so fail explicitly
  const exited = new Promise<never>((_, reject) =>
    child.once('exit', code =>
      reject(new Error(`Lean server exited with code ${code}`)),
    ),
  )
  const lspReady = Promise.race([handshake, exited])
  // the real error surfaces to whoever awaits `lspReady`; this just stops
  // Node from complaining about an unhandled rejection in the meantime
  lspReady.catch(() => {})

  const instance: LeanInstance = {
    id: randomUUID(),
    gamePath,
    gamePathBwrap: noBwrap ? gamePath : '/game',
    process: child,
    status: 'starting',
    startedAt: new Date(),
    exitCode: null,
    lastActivityAt: Date.now(),
    client,
    lspReady,
    game,
  }

  child.stderr.on('data', (chunk: Buffer) => {
    console.error(`[lean:${instance.id}] ${chunk.toString()}`)
  })

  child.once('spawn', () => {
    instance.status = 'running'
  })

  child.once('exit', code => {
    instance.status = 'exited'
    instance.exitCode = code
    instance.exitedAt ??= Date.now()
    forgetInstanceDocs(instance.id)
  })

  child.once('error', err => {
    instance.status = 'exited'
    instance.exitedAt ??= Date.now()
    console.error(`[lean:${instance.id}] failed to start:`, err)
  })

  instances.set(instance.id, instance)
  return instance
}

export function getInstance(id: string): LeanInstance | undefined {
  return instances.get(id)
}

// TODO: this is for debugging only. We should remove it eventually
export function getAllInstances(): LeanInstance[] {
  return Array.from(instances.values())
}

/** The number of instances which have not exited */
export function countActiveInstances(): number {
  let count = 0
  for (const instance of instances.values()) {
    if (instance.status !== 'exited') count++
  }
  return count
}

/** Marks the instance as active, returns `false` if it doesn't exist or has exited */
export function touchInstance(id: string): boolean {
  const instance = instances.get(id)
  if (!instance || instance.status === 'exited') return false
  instance.lastActivityAt = Date.now()
  return true
}

export function stopInstance(id: string): boolean {
  const instance = instances.get(id)
  if (!instance) return false

  if (instance.status !== 'exited') {
    instance.process.kill('SIGTERM')
  }
  return true
}

/** Stops all running instances of a game, returns how many were stopped */
export function stopGameInstances(gamePath: string): number {
  let stopped = 0
  for (const instance of instances.values()) {
    if (instance.gamePath === gamePath && instance.status !== 'exited') {
      instance.process.kill('SIGTERM')
      stopped++
    }
  }
  return stopped
}

// Stops the instances of players who have left without stopping their instance, e.g. by
// closing the tab, and forgets instances which have exited a while ago
setInterval(() => {
  const now = Date.now()
  for (const instance of instances.values()) {
    if (instance.status !== 'exited') {
      if (now - instance.lastActivityAt > IDLE_MS) {
        console.log(`[lean:${instance.id}] stopping idle instance`)
        stopInstance(instance.id)
      }
    } else if (now - (instance.exitedAt ?? now) > IDLE_MS) {
      instances.delete(instance.id)
    }
  }
}, CLEANUP_INTERVAL_MS).unref()
