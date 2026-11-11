import { existsSync, readdirSync } from 'node:fs'
import fs from 'node:fs/promises'
import path from 'node:path'

import type { Response } from 'express'

import type { ApiGameData, ApiGameInfo } from './api.js'
import { readConfig } from './config.js'
import { importedGamePath, importedGames } from './import/imported.js'
import { isDevMode } from './utils/devMode.js'
import { subfolders } from './utils/fs.js'
import { safeJoin } from './utils/path.js'

const TEST_GAME_PATH = path.resolve(
  import.meta.dirname,
  '..',
  '..',
  'GameSkeleton',
)
const REPO_PARENT_DIR = path.resolve(import.meta.dirname, '..', '..', '..')

/** The TestGame is only available as `test/testgame` */
export function isTestGame(owner: string, game: string) {
  return owner.toLowerCase() === 'test' && game.toLowerCase() === 'testgame'
}

/** returns the path to the game or writes a 404 if the game has not been found */
export function requireGame(owner: string, game: string, res: Response) {
  if (isTestGame(owner, game)) {
    return TEST_GAME_PATH
  }

  if (owner.toLowerCase() === 'local') {
    if (isDevMode()) {
      // the game in the URL is lowercase, the folder may not be
      const folder = readdirSync(REPO_PARENT_DIR).find(
        name => name.toLowerCase() === game.toLowerCase(),
      )
      const localPath = folder && safeJoin(REPO_PARENT_DIR, folder)
      if (localPath && existsSync(localPath)) return localPath
    }
    res.status(404).json({ error: 'Game not found' })
    return undefined
  }

  const gamePath = importedGamePath(owner, game)
  if (gamePath && existsSync(gamePath)) return gamePath

  res.status(404).json({ error: 'Game not found' })
  return undefined
}

export function gameDataFilePath(gamePath: string, filename: string) {
  return safeJoin(gamePath, '.lake', 'gamedata', filename)
}

export function i18nFilePath(gamePath: string, lang: string) {
  return safeJoin(gamePath, '.i18n', lang, 'Game.json')
}

/**
 * The games for the landing page: the featured games of the config, in dev mode the
 * GameSkeleton (as `test/testgame`) and the local games next to this repository, and if
 * the config allows it all other imported games. Games without a `game.json` are skipped.
 */
export async function listGames(): Promise<ApiGameInfo[]> {
  const config = await readConfig()
  const games: ApiGameInfo[] = []

  function add(game: ApiGameInfo | undefined) {
    if (game) games.push(game)
  }

  const featured = new Set<string>()
  for (const entry of config.featuredGames) {
    // the games/ folders are lower case
    const owner = entry.owner.toLowerCase()
    const repo = entry.repo.toLowerCase()
    const gamePath = importedGamePath(owner, repo)
    if (featured.has(`${owner}/${repo}`) || !gamePath) continue
    featured.add(`${owner}/${repo}`)
    add(await gameInfo(owner, repo, gamePath, true))
  }

  if (isDevMode()) {
    add(await gameInfo('test', 'testgame', TEST_GAME_PATH, false))
    for (const repo of await subfolders(REPO_PARENT_DIR)) {
      add(
        await gameInfo('local', repo, path.join(REPO_PARENT_DIR, repo), false),
      )
    }
  }

  if (config.listImportedGames) {
    for (const { owner, repo, gamePath } of await importedGames()) {
      if (featured.has(`${owner}/${repo}`)) continue
      add(await gameInfo(owner, repo, gamePath, false))
    }
  }
  return games
}

/**
 * Read the `game.json` to send the tiles and setting of the featured games
 * to the landing page
 */
async function gameInfo(
  owner: string,
  repo: string,
  gamePath: string,
  featured: boolean,
): Promise<ApiGameInfo | undefined> {
  const filePath = gameDataFilePath(gamePath, 'game.json')
  if (!filePath) return undefined
  const gameJson = await fs
    .readFile(filePath, 'utf-8')
    .then(content => JSON.parse(content) as ApiGameData)
    .catch(() => undefined)
  if (!gameJson) return undefined
  return {
    owner,
    repo,
    featured,
    tile: gameJson.tile ?? null,
    settings: gameJson.settings ?? null,
  }
}
