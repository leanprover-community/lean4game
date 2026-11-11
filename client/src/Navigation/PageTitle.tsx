import { useAtomValue } from 'jotai'
import { twMerge } from 'tailwind-merge'

import { gameIdAtom, levelIdAtom, worldIdAtom } from '../state/location-atoms'
import { gameInfoAtom, levelInfoAtom } from '../state/query-atoms'
import { useGameTranslation } from '../utils/translation'

/** The current game's info, world and level, and the translation of its texts */
function useGameTexts() {
  const gameId = useAtomValue(gameIdAtom)
  const levelId = useAtomValue(levelIdAtom)
  const { data: gameInfo } = useAtomValue(gameInfoAtom)
  const { t: gameT } = useGameTranslation(
    gameId ?? '',
    gameInfo?.settings?.allowEmptyTranslations,
  )
  const world = useAtomValue(worldIdAtom)
  const worldTitle = world
    ? gameT(gameInfo?.worlds?.nodes[world]?.title ?? world)
    : undefined
  return { gameId, gameInfo, gameT, levelId, world, worldTitle }
}

/**
 * The title in the middle of the app bar: the game's title on the game overview, the
 * world's title on a world, and e.g. `1/4: Level title` on a level.
 */
export function PageTitle() {
  const { gameId, gameInfo, gameT, levelId, world, worldTitle } = useGameTexts()
  const { data: levelInfo } = useAtomValue(levelInfoAtom)

  let title: string | undefined
  if (world !== undefined && levelId !== undefined) {
    const worldSize = gameInfo?.worldSize?.[world]
    const number =
      worldSize === undefined ? `${levelId}` : `${levelId}/${worldSize}`
    title = levelInfo?.title ? `${number}: ${gameT(levelInfo.title)}` : number
  } else if (world !== undefined) {
    title = worldTitle
  } else if (gameId !== undefined && gameInfo?.title) {
    title = gameT(gameInfo.title)
  }
  if (!title) return null
  return (
    <h1
      className={twMerge(
        'm-0 min-w-0 truncate text-center text-lg leading-normal font-bold',
        'text-white',
      )}
      title={title}
    >
      {title}
    </h1>
  )
}

/** The world's title on the left of the app bar on a level, only on desktop */
export function WorldTitle() {
  const { levelId, worldTitle } = useGameTexts()
  if (levelId === undefined || !worldTitle) return null
  return (
    // a grid has no minimal width when its content is truncated, so the title shrinks
    // instead of widening the button group and pushing the centered title over it
    <span className="grid min-w-0">
      <span className="truncate px-2 font-bold" title={worldTitle}>
        {worldTitle}
      </span>
    </span>
  )
}
