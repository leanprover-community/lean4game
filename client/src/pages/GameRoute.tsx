import { useAtomValue } from 'jotai'
import type { ReactNode } from 'react'

import { NotFound } from '../ErrorPage/NotFound'
import { levelIdAtom, routeAtom, worldIdAtom } from '../state/location-atoms'
import { gameInfoAtom } from '../state/query-atoms'
import { HttpError } from '../utils/fetch'

/**
 * Shows `children`, a page of a game, its world or its level, once the game is loaded,
 * and the 404 page if the game, the world or the level does not exist.
 */
export function GameRoute({ children }: { children: ReactNode }) {
  const route = useAtomValue(routeAtom)
  const { data: gameInfo, error } = useAtomValue(gameInfoAtom)
  const worldId = useAtomValue(worldIdAtom)
  const levelId = useAtomValue(levelIdAtom)

  if (error) {
    if (error instanceof HttpError && error.status === 404) return <NotFound />
    // e.g. the server is down, shown by the `ErrorBoundary`
    throw error
  }
  if (!gameInfo) return null
  // the URL has a world, but the game does not
  if ('world' in route && worldId === undefined) return <NotFound />
  if (
    levelId !== undefined &&
    levelId > (worldId ? (gameInfo.worldSize?.[worldId] ?? 0) : 0)
  )
    return <NotFound />
  return children
}
