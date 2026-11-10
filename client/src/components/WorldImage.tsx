import { useAtomValue } from 'jotai'
import { twMerge } from 'tailwind-merge'

import { gameIdAtom, worldIdAtom } from '../state/location-atoms'
import { gameInfoAtom } from '../state/query-atoms'
import { gameDataUrl } from '../utils/fetch'

/**
 * The image of the current world, filling its positioned parent as a background: fit
 * into it and aligned at the top, unless `className` says otherwise.
 */
export function WorldImage({ className }: { className?: string }) {
  const gameId = useAtomValue(gameIdAtom)
  const worldId = useAtomValue(worldIdAtom)
  const { data: gameInfo } = useAtomValue(gameInfoAtom)
  const image =
    worldId === undefined ? undefined : gameInfo?.worlds?.nodes[worldId]?.image
  if (!gameId || !image) return null
  return (
    <img
      className={twMerge(
        'absolute inset-0 size-full object-contain object-top',
        className,
      )}
      src={gameDataUrl(gameId, image)}
      alt=""
    />
  )
}
