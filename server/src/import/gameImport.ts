import { spawn, type ChildProcessWithoutNullStreams } from 'node:child_process'
import { createWriteStream, existsSync } from 'node:fs'
import fs from 'node:fs/promises'
import path from 'node:path'
import { Readable, Transform } from 'node:stream'
import { pipeline } from 'node:stream/promises'
import type { ReadableStream as NodeReadableStream } from 'node:stream/web'

import { addImport } from '../database/db.js'
import { gameDataFilePath } from '../gameData.js'
import { stopGameInstances } from '../lean/leanInstances.js'
import { spawnGame } from '../lean/sandbox.js'
import { GAMES_DIR, importedGamePath } from './imported.js'
import { type ImportRateLimitHit, takeImportSlot } from './rateLimit.js'

/*
Imports a game from GitHub: the game's repository builds the game in a GitHub action and
uploads the built folder (including `.lake`) as an artifact. The import downloads the newest
artifact, unpacks it into `games/<owner>/<repo>`, and installs the Lean toolchain.

Checks never build anything (see `dependencyBuildMode` in `openDocuments.ts`), so the import
verifies with `lake build --no-build` that the artifact is fully built and warns otherwise.
*/

const GITHUB_API_URL = process.env.GITHUB_API_URL || 'https://api.github.com'
const TOKEN = process.env.LEANGAME_GITHUB_TOKEN
const USER_AGENT = process.env.LEANGAME_GITHUB_USER || 'leangame'
const MB = 1024 * 1024
const MAX_DOWNLOAD_BYTES =
  (Number(process.env.IMPORT_MAX_DOWNLOAD_MB) || 8192) * MB
const MAX_UNPACKED_BYTES =
  (Number(process.env.IMPORT_MAX_UNPACKED_MB) || 40_960) * MB

/** Temporary files of running imports. Owners can't start with a dot on GitHub. */
const IMPORT_TMP_DIR = path.join(GAMES_DIR, '.import')

/** GitHub user and repository names */
const NAME_REGEX = /^[A-Za-z0-9_-][A-Za-z0-9_.-]*$/
/** e.g. `leanprover/lean4:v4.34.0` */
const TOOLCHAIN_REGEX = /^[A-Za-z0-9_.\-/:+]+$/

export interface ImportStatus {
  state: 'running' | 'done' | 'failed'
  startedAt: Date
  /** output of the import steps */
  log: string[]
  /** problems which don't stop the import, e.g. an incompletely built game */
  warnings: string[]
  /** progress of the artifact download, updated while downloading */
  download?: { receivedBytes: number; totalBytes: number }
}

const imports = new Map<string, ImportStatus>()

function importKey(owner: string, repo: string) {
  return `${owner.toLowerCase()}/${repo.toLowerCase()}`
}

export function isValidRepoName(owner: string, repo: string): boolean {
  return NAME_REGEX.test(owner) && NAME_REGEX.test(repo)
}

export function getImportStatus(
  owner: string,
  repo: string,
): ImportStatus | undefined {
  return imports.get(importKey(owner, repo))
}

/**
 * Starts importing the game unless an import of it is already running, which is returned
 * then. If the game has been imported too often, nothing is started and the limit returned.
 */
export function startImport(
  owner: string,
  repo: string,
): ImportStatus | ImportRateLimitHit {
  const key = importKey(owner, repo)
  const running = imports.get(key)
  if (running?.state === 'running') return running

  const limit = takeImportSlot(key)
  if (limit) {
    console.warn(
      `[import] ${key}: rate limit of ${limit.label} reached, possible again in ${limit.retryAfterSeconds} s`,
    )
    return limit
  }

  const status: ImportStatus = {
    state: 'running',
    startedAt: new Date(),
    log: [],
    warnings: [],
  }
  imports.set(key, status)
  doImport(owner, repo, status).then(
    () => {
      status.state = 'done'
      status.log.push('Done!')
    },
    (error: Error) => {
      status.state = 'failed'
      status.log.push(`Error: ${error.message}`)
    },
  )
  return status
}

async function doImport(owner: string, repo: string, status: ImportStatus) {
  const log = (line: string) => status.log.push(line)
  const targetPath = importedGamePath(owner, repo)
  if (!targetPath) throw new Error('Invalid repository name')
  if (!TOKEN) {
    throw new Error('The server has no GitHub token')
  }

  const artifact = await newestArtifact(owner, repo)
  log(`Found artifact ${artifact.id} from ${artifact.created_at}.`)

  const tmpPath = path.join(
    IMPORT_TMP_DIR,
    `${owner.toLowerCase()}_${repo.toLowerCase()}_${artifact.id}`,
  )
  await fs.rm(tmpPath, { recursive: true, force: true })
  await fs.mkdir(tmpPath, { recursive: true })
  try {
    const zipPath = path.join(tmpPath, 'artifact.zip')
    log(`Downloading ${formatMB(artifact.size_in_bytes)}...`)
    let loggedPercent = 0
    await download(
      artifact.archive_download_url,
      zipPath,
      (receivedBytes, totalBytes) => {
        status.download = { receivedBytes, totalBytes }
        // also log every 10%, so the log shows how the download went
        const percent = Math.floor((receivedBytes / totalBytes) * 10) * 10
        if (percent > loggedPercent) {
          loggedPercent = percent
          log(
            `Downloaded ${Math.min(percent, 100)}% (${formatMB(receivedBytes)} of ${formatMB(totalBytes)})`,
          )
        }
      },
      artifact.size_in_bytes,
    )

    const gamePath = await unpackArtifact(zipPath, tmpPath, log)
    await checkSymlinks(gamePath)
    if (!existsSync(gameDataFilePath(gamePath, 'game.json')!)) {
      throw new Error(
        'The artifact does not contain `.lake/gamedata/game.json`',
      )
    }

    const toolchain = await installToolchain(gamePath, log)
    const fullyBuilt = await checkFullyBuilt(gamePath, status)

    const stopped = stopGameInstances(targetPath)
    if (stopped > 0) log(`Stopped ${stopped} running instance(s) of the game.`)
    await replaceGame(gamePath, targetPath, tmpPath)
    log(`Installed the game in ${path.relative(GAMES_DIR, targetPath)}.`)
    addImport({ owner, repo, artifactId: artifact.id, toolchain, fullyBuilt })
  } finally {
    await fs.rm(tmpPath, { recursive: true, force: true })
  }
}

interface Artifact {
  id: number
  size_in_bytes: number
  archive_download_url: string
  created_at: string
  expired: boolean
}

function githubHeaders() {
  return {
    Accept: 'application/vnd.github+json',
    Authorization: `Bearer ${TOKEN}`,
    'User-Agent': USER_AGENT,
    'X-GitHub-Api-Version': '2022-11-28',
  }
}

async function newestArtifact(owner: string, repo: string): Promise<Artifact> {
  const url = `${GITHUB_API_URL}/repos/${owner}/${repo}/actions/artifacts?per_page=100`
  const res = await fetch(url, { headers: githubHeaders() })
  if (!res.ok) {
    throw new Error(
      `Could not list the artifacts of ${owner}/${repo} (${res.status})`,
    )
  }
  const { artifacts } = (await res.json()) as { artifacts: Artifact[] }
  const newest = artifacts
    .filter(artifact => !artifact.expired)
    .reduce<Artifact | undefined>(
      (acc, cur) => (!acc || acc.created_at < cur.created_at ? cur : acc),
      undefined,
    )
  if (!newest) {
    throw new Error(
      `${owner}/${repo} has no artifact. Did the GitHub action run?`,
    )
  }
  if (newest.size_in_bytes > MAX_DOWNLOAD_BYTES) {
    throw new Error(
      `The artifact exceeds the maximal size of ${MAX_DOWNLOAD_BYTES / MB} MB`,
    )
  }
  return newest
}

function formatMB(bytes: number) {
  return `${(bytes / MB).toFixed(1)} MB`
}

/** Downloads `url` to `dest`, aborting when it exceeds `MAX_DOWNLOAD_BYTES` */
async function download(
  url: string,
  dest: string,
  onProgress: (receivedBytes: number, totalBytes: number) => void,
  /** the expected size, if the response doesn't state it */
  expectedBytes: number,
) {
  // GitHub redirects to a signed URL, `fetch` drops the token on that redirect
  const res = await fetch(url, { headers: githubHeaders() })
  if (!res.ok || !res.body) {
    throw new Error(
      `Could not download the artifact (${res.status}). Is it expired?`,
    )
  }
  const totalBytes = Number(res.headers.get('content-length')) || expectedBytes
  let received = 0
  onProgress(0, totalBytes)
  const limit = new Transform({
    transform(chunk: Buffer, _encoding, callback) {
      received += chunk.length
      if (received > MAX_DOWNLOAD_BYTES) {
        callback(
          new Error(
            `The artifact exceeds the maximal size of ${MAX_DOWNLOAD_BYTES / MB} MB`,
          ),
        )
      } else {
        onProgress(received, totalBytes)
        callback(null, chunk)
      }
    },
  })
  await pipeline(
    Readable.fromWeb(res.body as NodeReadableStream),
    limit,
    createWriteStream(dest),
  )
}

/**
 * GitHub wraps the uploaded files in a zip. The game's action uploads the game as a zip
 * itself, so the artifact usually contains exactly one inner zip, which is unpacked too.
 * Returns the folder containing the game.
 */
async function unpackArtifact(
  zipPath: string,
  tmpPath: string,
  log: (line: string) => void,
): Promise<string> {
  const outerPath = path.join(tmpPath, 'artifact')
  await unzip(zipPath, outerPath)
  const files = await fs.readdir(outerPath)
  if (files.length !== 1 || !files[0].endsWith('.zip')) {
    log('Unpacked the artifact.')
    return outerPath
  }
  const gamePath = path.join(tmpPath, 'game')
  await unzip(path.join(outerPath, files[0]), gamePath)
  log(`Unpacked the artifact and ${files[0]}.`)
  return gamePath
}

async function unzip(zipPath: string, dest: string) {
  // `unzip -Zt` prints e.g. "12 files, 34567 bytes uncompressed, ..."
  const { output } = await run(spawn('unzip', ['-Zt', zipPath]))
  const match = /(\d+) bytes uncompressed/.exec(output)
  if (!match) throw new Error(`${path.basename(zipPath)} is not a valid zip`)
  if (Number(match[1]) > MAX_UNPACKED_BYTES) {
    throw new Error(
      `The unpacked artifact exceeds the maximal size of ${MAX_UNPACKED_BYTES / MB} MB`,
    )
  }
  // `unzip` skips entries with `..` or absolute paths
  const { code } = await run(spawn('unzip', ['-q', '-o', zipPath, '-d', dest]))
  if (code !== 0) throw new Error(`Could not unpack ${path.basename(zipPath)}`)
}

/** Rejects symlinks pointing outside the game, as the data endpoints follow them */
async function checkSymlinks(gamePath: string) {
  const root = await fs.realpath(gamePath)
  for (const entry of await fs.readdir(gamePath, {
    recursive: true,
    withFileTypes: true,
  })) {
    if (!entry.isSymbolicLink()) continue
    const linkPath = path.join(entry.parentPath, entry.name)
    const target = await fs.realpath(linkPath).catch(() => undefined)
    if (!target || (target !== root && !target.startsWith(root + path.sep))) {
      throw new Error(
        `The artifact contains a symlink pointing outside the game: ${path.relative(gamePath, linkPath)}`,
      )
    }
  }
}

/** Installs the game's toolchain and returns it */
async function installToolchain(
  gamePath: string,
  log: (line: string) => void,
): Promise<string> {
  const toolchain = (
    await fs.readFile(path.join(gamePath, 'lean-toolchain'), 'utf-8')
  ).trim()
  if (!TOOLCHAIN_REGEX.test(toolchain)) {
    throw new Error(`Invalid lean-toolchain: ${toolchain}`)
  }
  log(`Installing toolchain ${toolchain}...`)
  const { code, output } = await run(
    spawn('elan', ['toolchain', 'install', toolchain]),
  )
  if (code !== 0) {
    throw new Error(`Could not install toolchain ${toolchain}:\n${output}`)
  }
  return toolchain
}

/**
 * Warns if building the game or the game server would need to compile anything, as checks
 * never build. Runs in the sandbox since Lake executes the game's `lakefile`.
 */
async function checkFullyBuilt(
  gamePath: string,
  status: ImportStatus,
): Promise<boolean> {
  let fullyBuilt = true
  // every check imports `GameServer`, which the game's default targets may not include
  for (const target of [[], ['GameServer']]) {
    const command = ['lake', 'build', '--no-build', ...target]
    const { code, output } = await run(spawnGame(gamePath, command))
    if (code !== 0) {
      fullyBuilt = false
      const name = target[0] ?? 'the game'
      status.warnings.push(
        `${name} is not fully built. Checks will fail until the artifact contains all build files.`,
      )
      status.log.push(`\`${command.join(' ')}\` failed:`, output.trim())
    }
  }
  if (fullyBuilt) status.log.push('The game is fully built.')
  return fullyBuilt
}

/** Moves the new game into place, replacing an older version */
async function replaceGame(
  gamePath: string,
  targetPath: string,
  tmpPath: string,
) {
  await fs.mkdir(path.dirname(targetPath), { recursive: true })
  if (existsSync(targetPath)) {
    await fs.rename(targetPath, path.join(tmpPath, 'old'))
  }
  await fs.rename(gamePath, targetPath)
}

/** Waits for a process to exit and collects its stdout and stderr */
function run(
  child: ChildProcessWithoutNullStreams,
): Promise<{ code: number | null; output: string }> {
  let output = ''
  child.stdout.on('data', (chunk: Buffer) => (output += chunk.toString()))
  child.stderr.on('data', (chunk: Buffer) => (output += chunk.toString()))
  return new Promise((resolve, reject) => {
    child.once('error', reject)
    child.once('close', code => resolve({ code, output }))
  })
}
