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
export const levelProgressAtomFamily = atomFamily((key: string) =>
  atom(get => {
    const [worldId, levelStr] = key.split(":")
    const levelId = Number(levelStr)
    const worldProgress = get(worldProgressAtomFamily(worldId))
    return worldProgress?.[levelId] ?? null
  })
)

/** Completion of a specific level */
export const levelCompletedAtomFamily = atomFamily((key: string) => atom<boolean>(get => {
  const [worldId, levelStr] = key.split(":")
  const levelId = Number(levelStr)
  if (levelId == 0) return true
  const levelProgress = get(levelProgressAtomFamily(key))
  return levelProgress?.completed ?? false
}))

/** The completion state of all levels */
export const levelsCompletedAtomFamily = atomFamily((worldId: string) => atom<boolean[]>(get => {
  const { data: gameInfo } = get(gameInfoAtom)
  const worldSize = gameInfo?.worldSize?.[worldId]
  return Array.from(Array(worldSize).keys()).map(i => (get(levelCompletedAtomFamily(`${worldId}: ${i}`))))
}))

/** A world is completed if all its levels are */
export const worldCompletedAtom = atomFamily((worldId: string) => atom<boolean>(get => {
  return (get(levelsCompletedAtomFamily(worldId)).every(it => it))
}))

/** The first uncompleted level or `0` */
export const firstIncompleteLevel = atomFamily((worldId: string) => atom<number>(get => {
  const firstIncompleteLevel = get(levelsCompletedAtomFamily(worldId)).findIndex(it => !it)
  // note: `findIndex` returns `-1` on failure, therefore the indices
  // `-1, 0, 1` indicate all that the introduction should be shown
  return firstIncompleteLevel >= 1 ? firstIncompleteLevel : 0
}))

/** A world is unlocked if all dependency worlds have been completed */
export const worldDependenciesCompletedAtomFamily = atomFamily((worldId: string) => atom<boolean>(get => {
  const { data: gameInfo } = get(gameInfoAtom)
  const prerequisitesCompleted: boolean[] = gameInfo?.worlds?.edges.filter(it => it[1] == worldId)?.map(it => {
    return get(worldCompletedAtom(worldId)) ?? false
  }) ?? []
  return prerequisitesCompleted.every(it => it)
}))
