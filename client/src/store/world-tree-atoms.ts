import { atom } from "jotai"
import { atomFamily } from "jotai/utils"
import { progressAtom } from "./progress-atoms"
import { gameInfoAtom, gameInfoAtomFamily } from "./query-atoms"

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

/** Whether the last level of each dependency has been completed */
export const worldDependenciesCompletedAtomFamily = atomFamily((worldId: string) => atom<boolean>(get => {
  const { data: gameInfo } = get(gameInfoAtom)
  const prerequisitesCompleted: boolean[] = gameInfo?.worlds?.edges.filter(it => it[1] == worldId)?.map(it => {
    const worldSizeDep = gameInfo?.worldSize?.[it[1]]
    return (worldSizeDep ? get(completedAtomFamily([worldId, worldSizeDep - 1])) : false) ?? false
  }) ?? []
  return prerequisitesCompleted.every(it => it)
}))

/**  */
export const completedAtomFamily = atomFamily((key: [string, number | null]) => atom<boolean>(get => {
  const worldId = key[0]
  const levelId = key[1]
  const { data: gameInfo } = get(gameInfoAtom)
  if (levelId !== null) {
    const levelProgress = get(levelProgressAtomFamily([worldId, levelId]))
    return levelProgress?.completed ?? false
  } else {
    // Check: all levels in the world are completed
    // and the last level of each prerequisite world
    const worldSize = gameInfo?.worldSize?.[worldId]
    const completedLevels: boolean[] = Array.from(Array(worldSize).keys()).map(i => (get(completedAtomFamily([worldId,i]))))
    const worldDependenciesCompleted: boolean = get(worldDependenciesCompletedAtomFamily(worldId))
    return completedLevels.every(it => it) && worldDependenciesCompleted
  }
}))
