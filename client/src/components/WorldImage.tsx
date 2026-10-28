import { useAtomValue } from 'jotai'

import { gameIdAtom, worldIdAtom } from '../state/location-atoms'
import { gameInfoAtom } from '../state/query-atoms'
import { gameDataUrl } from '../utils/fetch'

/**
 * The image of the current world, filling its positioned parent as a background: fit
 * into it and aligned at the top.
 */
export function WorldImage() {
  const gameId = useAtomValue(gameIdAtom)
  const worldId = useAtomValue(worldIdAtom)
  const { data: gameInfo } = useAtomValue(gameInfoAtom)
  const image =
    worldId === undefined ? undefined : gameInfo?.worlds?.nodes[worldId]?.image
  if (!gameId || !image) return null
  return (
    <img
      className="absolute inset-0 size-full object-contain object-top"
      src={gameDataUrl(gameId, image)}
      alt=""
    />
  )
}
