import { atom } from 'jotai'
import { atomWithQuery } from 'jotai-tanstack-query'

import type { ApiLevelData } from '../api'
import { fetchJson, gameDataUrl, retryUnlessClientError } from '../utils/fetch'
import { gameInfoAtomFamily } from './game-info-atoms'
import { gameIdAtom, levelIdAtom, worldIdAtom } from './location-atoms'

export { gameInfoAtomFamily }

/** The info about the current game */
export const gameInfoAtom = atom(get => {
  const gameId = get(gameIdAtom)
  return get(gameInfoAtomFamily(gameId ?? ''))
})

/**
 * The conclusion of the current world, empty if it has none. If it has one, it is shown
 * on its own page after the last level.
 */
export const worldConclusionAtom = atom(get => {
  const worldId = get(worldIdAtom)
  if (worldId === undefined) return ''
  const world = get(gameInfoAtom).data?.worlds?.nodes[worldId]
  return world?.conclusion?.trim() ?? ''
})

/** Info about the current level */
export const levelInfoAtom = atomWithQuery<ApiLevelData>(get => {
  const gameId = get(gameIdAtom)
  const worldId = get(worldIdAtom)
  const levelId = get(levelIdAtom)
  return {
    queryKey: ['levelInfo', gameId, worldId, levelId],
    queryFn: () =>
      fetchJson<ApiLevelData>(
        gameDataUrl(
          gameId!,
          `level/${encodeURIComponent(worldId!)}/${levelId}`,
        ),
      ),
    retry: retryUnlessClientError,
    enabled:
      gameId !== undefined && worldId !== undefined && levelId !== undefined,
  }
})
