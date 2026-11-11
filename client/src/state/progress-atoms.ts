import { atom } from 'jotai'
import { atomWithStorage, createJSONStorage } from 'jotai/utils'

import { downloadFile } from '../utils/download'
import { gameIdAtom, levelIdAtom, worldIdAtom } from './location-atoms'
import { migrateStoredProgress } from './progress-migration'
import {
  type GameProgress,
  type LevelProgress,
  type Progress,
  type WorldProgress,
  DEFAULT_DIFFICULTY,
} from './progress-types'

/**
 * The player's progress is stored in local storage under `game_progress`.
 *
 * The atoms here deal with reading from and writing to local storage.
 */

const defaultProgress: Progress = {
  games: {},
}

export const defaultWorldProgress: WorldProgress = { readIntro: false }

export const defaultLevelProgress: LevelProgress = {
  proof: [],
  selections: [],
  completed: false,
  help: [],
}

const defaultGameProgress: GameProgress = {
  inventory: [],
  data: {},
  readIntro: false,
  difficulty: DEFAULT_DIFFICULTY,
}

const PROGRESS_KEY = 'game_progress'

const storage = createJSONStorage<Progress>(() => localStorage)

// before the progress is read below
migrateStoredProgress(PROGRESS_KEY)

/**
 * This handles all progress for all games.
 * Therefore this must not be exported so that no game can interfer with any other game.
 */
const allProgressAtom = atomWithStorage<Progress>(
  PROGRESS_KEY,
  defaultProgress,
  storage,
  { getOnInit: true },
)

/** Access to the progress of the current game in local storage */
export const progressAtom = atom(
  get => {
    const gameId = get(gameIdAtom)
    console.debug(`progress for ${gameId}`)
    if (!gameId) return null
    const allProgress = get(allProgressAtom)
    return allProgress.games[gameId] ?? defaultGameProgress
  },
  (get, set, val: GameProgress | null) => {
    const gameId = get(gameIdAtom)
    if (!gameId) return
    set(allProgressAtom, prev => {
      const games = { ...prev.games }
      if (val) {
        games[gameId] = val
      } else {
        delete games[gameId]
      }
      return { ...prev, games }
    })
  },
)

/** The current world progress */
export const worldProgressAtom = atom(
  get => {
    const worldId = get(worldIdAtom)
    const progress = get(progressAtom)
    if (!worldId || !progress) return null
    return progress.data[worldId] ?? defaultWorldProgress
  },
  (get, set, val: WorldProgress | null) => {
    const worldId = get(worldIdAtom)
    const progress = get(progressAtom)
    if (!worldId || !progress) return
    const allWorlds = { ...progress.data }
    if (val) {
      allWorlds[worldId] = val
    } else {
      delete allWorlds[worldId]
    }
    set(progressAtom, { ...progress, data: allWorlds })
  },
)

/** The current level progress */
export const levelProgressAtom = atom(
  get => {
    const levelId = get(levelIdAtom)
    const worldProgress = get(worldProgressAtom)
    if (levelId == null || !worldProgress) return null
    return worldProgress[levelId] ?? defaultLevelProgress
  },
  (get, set, val: LevelProgress | null) => {
    const levelId = get(levelIdAtom)
    const worldProgress = get(worldProgressAtom)
    if (levelId == null) return
    const copied = { ...(worldProgress ?? defaultWorldProgress) }
    if (val) {
      copied[levelId] = val
    } else {
      delete copied[levelId]
    }
    set(worldProgressAtom, copied)
  },
)

/** The selected difficulty for the current game */
export const difficultyAtom = atom(
  get => {
    const progress = get(progressAtom)
    return progress?.difficulty ?? DEFAULT_DIFFICULTY
  },
  (get, set, val: number) => {
    const progress = get(progressAtom)
    console.debug(progress)
    if (!progress) return
    if (val < 0 || val > 2) {
      console.error('Cannot set difficulty outside of 0, 1, 2!')
      return
    }
    set(progressAtom, { ...progress, difficulty: val })
  },
)

export const readWorldIntroAtom = atom(null, (get, set) => {
  const worldProgress = get(worldProgressAtom)
  if (worldProgress == null) return
  set(worldProgressAtom, { ...worldProgress, readIntro: true })
})

export const completedAtom = atom(
  get => {
    const levelProgress = get(levelProgressAtom)
    return levelProgress?.completed ?? false
  },
  (get, set, val: boolean) => {
    const levelProgress = get(levelProgressAtom)
    if (levelProgress == null) return
    set(levelProgressAtom, { ...levelProgress, completed: val })
  },
)

/** Lets the player save the progress of the current game as a JSON file */
export const downloadProgressAtom = atom(null, get => {
  const gameId = get(gameIdAtom)
  const progress = get(progressAtom)
  if (!gameId || !progress) return
  // e.g. `leangame-owner-repo-2026-10-27.json`
  const game = gameId.replace(/^g\//, '').replace('/', '-')
  const date = new Date().toISOString().slice(0, 10)
  downloadFile(
    JSON.stringify(progress, null, 2),
    `leangame-${game}-${date}.json`,
    'application/json',
  )
})
