import { gameProgressSchema } from './progress-schema'
import type {
  GameProgress,
  LevelProgress,
  Progress,
  WorldProgress,
} from './progress-types'

/*
The old client used the same storage key and format, apart from two things:

- It stored the progress under the game as written in the URL, e.g.
  `g/leanprover-community/NNG4`. Now game IDs are lowercase, so the progress is moved to
  the lowercase key. Entries of the same game in different spellings are merged.
- Its older versions wrote less, e.g. levels without `help`, which it tolerated when
  reading. These fields get their defaults, the same as in an uploaded file.

A game which does not match the format stays as it is under its key, so that it is
not lost and does not stop the other games from being migrated.
*/

/** `a` with what `b` has in addition, e.g. levels only completed in `b` */
function mergeGameProgress(a: GameProgress, b: GameProgress): GameProgress {
  const data: GameProgress['data'] = { ...a.data }
  for (const [world, worldB] of Object.entries(b.data)) {
    const worldA = data[world] as WorldProgress | undefined
    if (!worldA) {
      data[world] = worldB
      continue
    }
    const merged: WorldProgress = {
      ...worldA,
      readIntro: worldA.readIntro || worldB.readIntro,
    }
    for (const [key, levelB] of Object.entries(worldB)) {
      if (key === 'readIntro') continue
      const level = Number(key)
      const levelA = merged[level] as LevelProgress | undefined
      if (!levelA || (!levelA.completed && (levelB as LevelProgress).completed))
        merged[level] = levelB as LevelProgress
    }
    data[world] = merged
  }
  return {
    ...b,
    ...a,
    inventory: [...new Set([...a.inventory, ...b.inventory])],
    readIntro: a.readIntro || b.readIntro,
    data,
  }
}

/** `progress` in the current format, see above, `undefined` if nothing changed */
export function migrateProgress(progress: Progress): Progress | undefined {
  const keys = Object.keys(progress.games)
  // the lowercase keys first, so that their settings, e.g. the difficulty, are kept
  keys.sort(
    (k1, k2) =>
      Number(k2 === k2.toLowerCase()) - Number(k1 === k1.toLowerCase()),
  )
  const games: Progress['games'] = {}
  const malformed = new Set<string>()
  for (const key of keys) {
    const id = key.toLowerCase()
    const game = gameProgressSchema.safeParse(progress.games[key])
    if (!game.success || malformed.has(id)) {
      if (!game.success) {
        malformed.add(key)
        console.warn(`Could not migrate the progress of ${key}`, game.error)
      }
      games[key] = progress.games[key]
      continue
    }
    games[id] =
      id in games ? mergeGameProgress(games[id], game.data) : game.data
  }
  const migrated = { ...progress, games }
  return JSON.stringify(migrated) === JSON.stringify(progress)
    ? undefined
    : migrated
}

/** Migrates the progress in local storage under `key`, see `migrateProgress` */
export function migrateStoredProgress(key: string) {
  try {
    const stored = localStorage.getItem(key)
    if (!stored) return
    const migrated = migrateProgress(JSON.parse(stored) as Progress)
    if (migrated) localStorage.setItem(key, JSON.stringify(migrated))
  } catch (error) {
    // e.g. local storage is not available, or holds something else
    console.warn('Could not migrate the progress', error)
  }
}
