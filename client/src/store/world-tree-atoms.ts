import { atom } from "jotai"
import { atomFamily } from "jotai/utils"
import { progressAtom } from "./progress-atoms"

/** World progress family */
export const worldProgressAtomFamily = atomFamily((worldId: string) => atom(get => {
  const progress = get(progressAtom)
  if (!progress) return null
  return progress.data[worldId]
}))

/** The current level progress */
export const levelProgressAtomFamily = atomFamily((key: [string, number]) => atom(get => {
  const worldId = key[0]
  const levelId = key[1]
  const worldProgress = get(worldProgressAtomFamily(worldId))
  if (!levelId || !worldProgress) return null
  return worldProgress[levelId]
}))

export const completedAtomFamily = atomFamily((key: [string, number | null]) => atom(get => {
  const worldId = key[0]
  const levelId = key[1]
  if (levelId !== null) {
    const levelProgress = get(levelProgressAtomFamily([worldId, levelId]))
    return levelProgress?.completed ?? false
  } else {
    // TODO: map over all levels of the worlds
    return false
  }

}))
