import { atom } from "jotai"
import { levelIdAtom, worldIdAtom } from "./location-atoms"
import { progressAtom, defaultLevelProgress, defaultWorldProgress } from "./progress-atoms"
import { GameProgress, LevelProgress, Progress, WorldProgress, Selection, DEFAULT_DIFFICULTY } from "./progress-types";

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
  }
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
    if (!levelId) return
    const copied = { ...(worldProgress ?? defaultWorldProgress) }
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
    if (!progress) return
    if (val < 0 || val > 2) {
      console.error("Cannot set difficulty outside of 0, 1, 2!")
      return
    }
    set(progressAtom, { ...progress, difficulty: val })
  }
)

/**
 * The user's unlocked inventory.
 * The setter adds the new constants to the existing inventory
 * ignoring duplicates.
 *  */
export const inventoryAtom = atom(
  get => {
    const progress = get(progressAtom)
    if (!progress) return null
    return progress.inventory
  },
  (get, set, val: string[]) => {
    const progress = get(progressAtom)
    if (!progress) return
    const newInventory = [...new Set([...progress.inventory, ...val])]
    set(progressAtom, { ...progress, inventory: newInventory })
  }
)

/** User read the game introduction. Only relevant on mobile */
export const readGameIntroAtom = atom(
  get => {
    const progress = get(progressAtom)
    if (!progress) return false
    return progress.readIntro
  },
  (get, set, val: boolean) => {
    const progress = get(progressAtom)
    if (!progress) return
    set(progressAtom, { ...progress, readIntro: val })
  }
)

/** Whether the current game is in typewriter mode */
export const typewriterModeAtom = atom(
  get => {
    const progress = get(progressAtom)
    if (!progress) return false
    return progress.typewriterMode
  },
  (get, set, val: boolean | null) => {
    const progress = get(progressAtom)
    if (!progress) return
    const valMod = (val === null) ? undefined : val
    set(progressAtom, { ...progress, typewriterMode: valMod })
  }
)

export const completedAtom = atom(
  get => {
    const levelProgress = get(levelProgressAtom)
    return levelProgress?.completed ?? false
  },
  (get, set, val: boolean) => {
    const levelProgress = get(levelProgressAtom) ?? defaultLevelProgress
    set(levelProgressAtom, { ...levelProgress, completed: val })
  }
)

export const codeAtom = atom(
  get => {
    const levelProgress = get(levelProgressAtom)
    return levelProgress?.code
  },
  (get, set, val: string) => {
    const levelProgress = get(levelProgressAtom) ?? defaultLevelProgress
    set(levelProgressAtom, { ...levelProgress, code: val })
  }
)

export const helpAtom = atom(
  get => {
    const levelProgress = get(levelProgressAtom)
    return levelProgress?.help ?? []
  },
  (get, set, val: number[]) => {
    const levelProgress = get(levelProgressAtom) ?? defaultLevelProgress
    set(levelProgressAtom, { ...levelProgress, help: val })
  }
)

export const selectionsAtom = atom(
  get => {
    const levelProgress = get(levelProgressAtom)
    return levelProgress?.selections ?? []
  },
  (get, set, val: Selection[]) => {
    const levelProgress = get(levelProgressAtom) ?? defaultLevelProgress
    set(levelProgressAtom, { ...levelProgress, selections: val })
  }
)
