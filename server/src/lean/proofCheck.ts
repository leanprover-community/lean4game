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
    'import GameServer\n' +
    `${originalContent}\n\n` +
    `Runner "${gameData.name}" "${world}" ${level} ` +
    `(difficulty := ${difficulty}) ` +
    `(inventory := ${inventoryFormatted}) ` +
    `:= by\n`
  const content = `${header}${tacticBlock}\n`
  // 0-based line of the first tactic
  const proofStartLine = header.split('\n').length - 1

  const uri = pathToFileURL(
    path.posix.join(instance.gamePathBwrap, modulePath),
  ).toString()

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
          gameId: gameData.name,
          worldId: world,
          levelId: level,
          proofStartLine,
          stepLines: steps.map(lines => lines.length),
          hovers: hovers,
        },
      },
    )
  } catch (error) {
    // start over with a fresh file worker on the next check
    await closeDoc(instance, uri, current.doc)
    // the RPC method is missing if the imports (including `GameServer`)
    // could not be loaded. Checks never build them, see `syncDoc`.
    if (
      error instanceof Error &&
      error.message.includes("No RPC method 'Game.checkProof'")
    ) {
      throw new Error(
        'Could not load the imports of the level. Is the game fully built?',
        { cause: error },
      )
    }
    throw error
  }
}
