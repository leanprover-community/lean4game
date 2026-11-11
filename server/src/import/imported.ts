import path from 'node:path'

import { subfolders } from '../utils/fs.js'
import { safeJoin } from '../utils/path.js'

export const GAMES_DIR = path.resolve(
  import.meta.dirname,
  '..',
  '..',
  process.env.GAMES_DIR ?? 'games',
)

/** All games in the games folder */
export async function importedGames() {
  const games: { owner: string; repo: string; gamePath: string }[] = []
  for (const owner of await subfolders(GAMES_DIR)) {
    for (const repo of await subfolders(path.join(GAMES_DIR, owner))) {
      games.push({ owner, repo, gamePath: path.join(GAMES_DIR, owner, repo) })
    }
  }
  return games
}

/** The folder of an imported game, or `undefined` for invalid names */
export function importedGamePath(owner: string, game: string) {
  return safeJoin(GAMES_DIR, owner.toLowerCase(), game.toLowerCase())
}
