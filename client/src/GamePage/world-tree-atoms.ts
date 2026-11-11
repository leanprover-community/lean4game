import { atom } from 'jotai'
import { atomFamily } from 'jotai-family'

import { progressAtom } from '../state/progress-atoms'
import { gameInfoAtom } from '../state/query-atoms'

/** The key `world:level` of a level for the atom families below */
export function levelKey(worldId: string, levelId: number) {
  return `${worldId}:${levelId}`
}

/** The world and level of a `levelKey`; world ids may contain `:` themselves */
function parseLevelKey(key: string): [string, number] {
  const i = key.lastIndexOf(':')
  return [key.slice(0, i), Number(key.slice(i + 1))]
}

/** World progress family */
export const worldProgressAtomFamily = atomFamily((worldId: string) =>
  atom(get => {
    const progress = get(progressAtom)
    if (!progress) return null
    return progress.data[worldId]
  }),
)

/** The progress of a level, by its `levelKey` */
export const levelProgressAtomFamily = atomFamily((key: string) =>
  atom(get => {
    const [worldId, levelId] = parseLevelKey(key)
    const worldProgress = get(worldProgressAtomFamily(worldId))
    return worldProgress?.[levelId] ?? null
  }),
)

/** Completion of a level, by its `levelKey`. Level 0, the introduction, is always completed */
export const levelCompletedAtomFamily = atomFamily((key: string) =>
  atom<boolean>(get => {
    const [, levelId] = parseLevelKey(key)
    if (levelId === 0) return true
    const levelProgress = get(levelProgressAtomFamily(key))
    return levelProgress?.completed ?? false
  }),
)

/** The completion state of the levels `1..N` of a world */
export const levelsCompletedAtomFamily = atomFamily((worldId: string) =>
  atom<boolean[]>(get => {
    const { data: gameInfo } = get(gameInfoAtom)
    const worldSize = gameInfo?.worldSize?.[worldId] ?? 0
    return Array.from({ length: worldSize }, (_, i) =>
      get(levelCompletedAtomFamily(levelKey(worldId, i + 1))),
    )
  }),
)

/** A world is completed if all its levels are */
export const worldCompletedAtom = atomFamily((worldId: string) =>
  atom<boolean>(get => {
    return get(levelsCompletedAtomFamily(worldId)).every(it => it)
  }),
)

/**
 * The level to continue a world with: the first uncompleted level, or `0`, the
 * introduction, if the player has not started the world yet or completed it.
 */
export const firstIncompleteLevelAtomFamily = atomFamily((worldId: string) =>
  atom<number>(get => {
    // note: `findIndex` returns `-1` on failure, so this is `0` if all are completed
    const firstIncompleteLevel =
      get(levelsCompletedAtomFamily(worldId)).findIndex(it => !it) + 1

    if (firstIncompleteLevel > 1) return firstIncompleteLevel

    const readIntro = get(worldProgressAtomFamily(worldId))?.readIntro

    return readIntro ? 1 : 0
  }),
)

/** A world is unlocked if all dependency worlds have been completed */
export const worldDependenciesCompletedAtomFamily = atomFamily(
  (worldId: string) =>
    atom<boolean>(get => {
      const { data: gameInfo } = get(gameInfoAtom)
      return (gameInfo?.worlds?.edges ?? [])
        .filter(([, target]) => target === worldId)
        .every(([source]) => get(worldCompletedAtom(source)))
    }),
)

/** The game is completed if it has worlds and all of them are */
export const gameCompletedAtom = atom<boolean>(get => {
  const { data: gameInfo } = get(gameInfoAtom)
  const worlds = Object.keys(gameInfo?.worlds?.nodes ?? {})
  return worlds.length > 0 && worlds.every(w => get(worldCompletedAtom(w)))
})
