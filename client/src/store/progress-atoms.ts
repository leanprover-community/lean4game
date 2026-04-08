import { atomWithStorage, createJSONStorage } from "jotai/utils";
import { GameProgress, LevelProgress, Progress, WorldProgress, Selection, DEFAULT_DIFFICULTY } from "./progress-types";
import { gameIdAtom, levelIdAtom, worldIdAtom } from "./location-atoms";
import { atom } from "jotai";

/**
 * The player's progress is stored in local storage under `game_progress`.
 *
 * The atoms here deal with reading from and writing to local storage.
 */

const defaultProgress: Progress = {
  games: {}
}

const defaultGameProgress: GameProgress =
  {inventory: [], data: {}, readIntro: false, difficulty: DEFAULT_DIFFICULTY}

const storage = createJSONStorage<Progress>(() => localStorage)

/**
 * This handles all progress for all games.
 * Therefore this must not be exported so that no game can interfer with any other game.
 */
const allProgressAtom = atomWithStorage<Progress>(
  'game_progress',
  defaultProgress,
  storage, { getOnInit: true }
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
  }
)

/** The current world progress */
export const worldProgressAtom = atom(
  get => {
    const worldId = get(worldIdAtom)
    const progress = get(progressAtom)
    if (!worldId || !progress) return null
    return progress.data[worldId]
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
  }
)

/** The current level progress */
export const levelProgressAtom = atom(
  get => {
    const levelId = get(levelIdAtom)
    const worldProgress = get(worldProgressAtom)
    if (!levelId || !worldProgress) return null
    return worldProgress[levelId]
  },
  (get, set, val: LevelProgress | null) => {
    const levelId = get(levelIdAtom)
    const worldProgress = get(worldProgressAtom)
    if (!levelId || !worldProgress) return
    const copied = { ...worldProgress }
    if (val) {
      copied[levelId] = val
    } else {
      delete copied[levelId]
    }
    set(worldProgressAtom, copied)
  }
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
      console.error("Cannot set difficulty outside of 0, 1, 2!")
      return
    }
    set(progressAtom, { ...progress, difficulty: val })
  }
)

export const completedAtom = atom(
  get => {
    const levelProgress = get(levelProgressAtom)
    return levelProgress?.completed ?? false
  },
  (get, set, val: boolean) => {
    const levelProgress = get(levelProgressAtom)
    if (!levelProgress) return
    set(levelProgressAtom, { ...levelProgress, completed: val })
  }
)
