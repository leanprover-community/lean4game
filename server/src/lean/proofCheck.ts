import { existsSync } from 'node:fs'
import fs from 'node:fs/promises'
import path from 'node:path'
import { pathToFileURL } from 'node:url'

import type { ApiProofCheckInput, ApiProofCheckResult } from '../api.js'
import { gameDataFilePath } from '../gameData.js'
import type { LeanInstance } from './leanInstances.js'
import {
  CheckTimeoutError,
  closeDoc,
  type OpenDoc,
  openDocIfClosed,
  scheduleCheck,
  syncDoc,
} from './openDocuments.js'

/** Extend the API-input with the Lean instance */
interface ProofCheck extends ApiProofCheckInput {
  instance: LeanInstance
}

async function readJson<T>(filePath: string): Promise<T> {
  const content = await fs.readFile(filePath, 'utf-8')
  return JSON.parse(content) as T
}

/** The document a running check is working on */
interface CheckDoc {
  uri?: string
  doc?: OpenDoc
  timedOut?: boolean
}

export function checkProof(input: ProofCheck): Promise<ApiProofCheckResult> {
  const current: CheckDoc = {}
  return scheduleCheck(
    input.instance.id,
    () => checkProofAux(input, current),
    () => {
      current.timedOut = true
      // stop the elaboration by killing the file worker
      if (current.uri) void closeDoc(input.instance, current.uri, current.doc)
    },
  )
}

/** The document of a level, before the `Runner` of a check is appended */
interface LevelDocument {
  uri: string
  /** `import GameServer` and the source of the level */
  source: string
  /** the name of the game as in `game.json` */
  gameName: string
}

async function levelDocument(
  instance: LeanInstance,
  world: string,
  level: number,
): Promise<LevelDocument> {
  const levelDataPath = gameDataFilePath(
    instance.gamePath,
    `level__${world}__${level}.json`,
  )
  const gameDataPath = gameDataFilePath(instance.gamePath, 'game.json')

  if (!levelDataPath || !gameDataPath) {
    throw new Error('Could not resolve level/game data paths')
  }
  if (!existsSync(levelDataPath)) {
    throw new Error(`Could not find world '${world}', level '${level}'.`)
  }
  if (!existsSync(gameDataPath)) {
    throw new Error(`Could not find the requested game.`)
  }
  const levelData = await readJson<{ module: string }>(levelDataPath)
  const gameData = await readJson<{ name: string }>(gameDataPath)

  const modulePath = levelData.module.split('.').join(path.sep) + '.lean'
  const sourcePath = path.join(instance.gamePath, modulePath)
  const originalContent = await fs.readFile(sourcePath, 'utf-8')

  const uri = pathToFileURL(
    path.posix.join(instance.gamePathBwrap, modulePath),
  ).toString()
  return {
    uri,
    source: `import GameServer\n${originalContent}\n\n`,
    gameName: gameData.name,
  }
}

/**
 * Opens the document of a level, so that Lean loads its imports, e.g. all of Mathlib,
 * before the player opens the level. Doesn't wait for Lean, and doesn't change the
 * document if it is open already. The first check only appends its `Runner`.
 */
export async function preloadLevel(
  instance: LeanInstance,
  world: string,
  level: number,
): Promise<void> {
  await instance.lspReady
  const { uri, source } = await levelDocument(instance, world, level)
  await openDocIfClosed(instance, uri, source)
}

async function checkProofAux(
  {
    difficulty,
    hovers = false,
    instance,
    inventory,
    level,
    tactics,
    world,
  }: ProofCheck,
  current: CheckDoc,
): Promise<ApiProofCheckResult> {
  await instance.lspReady
  const { uri, source, gameName } = await levelDocument(instance, world, level)

  // each tactic is a step of the proof, it may span several lines, e.g.
  // `have h : P := by\n  simp`
  const steps = tactics
    .map(tactic => tactic.trimEnd().split('\n'))
    .filter(lines => lines.some(line => line.trim().length > 0))
  const tacticBlock = steps
    .flat()
    .map(line => '  ' + line)
    .join('\n')
  const inventoryFormatted =
    '[' + inventory.map(name => JSON.stringify(name)).join(', ') + ']'
  const header =
    source +
    `Runner "${gameName}" "${world}" ${level} ` +
    `(difficulty := ${difficulty}) ` +
    `(inventory := ${inventoryFormatted}) ` +
    `:= by\n`
  const content = `${header}${tacticBlock}\n`
  // 0-based line of the first tactic
  const proofStartLine = header.split('\n').length - 1

  // a newer check may already be using the document
  if (current.timedOut) throw new CheckTimeoutError()
  current.uri = uri
  try {
    current.doc = await syncDoc(instance, uri, content)
    const { version } = current.doc
    await instance.client.request('textDocument/waitForDiagnostics', {
      uri,
      version,
    })

    const position = { line: proofStartLine, character: 0 }
    const { sessionId } = await instance.client.request<{
      sessionId: number | string
    }>('$/lean/rpc/connect', { uri })
    return await instance.client.request<ApiProofCheckResult>(
      '$/lean/rpc/call',
      {
        textDocument: { uri },
        position,
        sessionId,
        method: 'Game.checkProof',
        params: {
          gameId: gameName,
          worldId: world,
          levelId: level,
          proofStartLine,
          stepLines: steps.map(lines => lines.length),
          hovers: hovers,
        },
      },
    )
  } catch (error) {
    // the RPC method is missing if the imports (including `GameServer`)
    // could not be loaded. Checks never build them, see `syncDoc`.
    const importsFailed =
      error instanceof Error &&
      error.message.includes("No RPC method 'Game.checkProof'")
    // start over with a fresh file worker on the next check. Otherwise keep the
    // document: opening it again would load the imports again, e.g. all of Mathlib
    if (importsFailed || isWorkerCrash(error)) {
      await closeDoc(instance, uri, current.doc)
    }
    if (importsFailed) {
      throw new Error(
        'Could not load the imports of the level. Is the game fully built?',
        { cause: error },
      )
    }
    throw error
  }
}

/** Lean's error code for a request to the file worker of a document which crashed */
const WORKER_CRASHED = -32_902

function isWorkerCrash(error: unknown): boolean {
  return (
    typeof error === 'object' &&
    error !== null &&
    'code' in error &&
    error.code === WORKER_CRASHED
  )
}
