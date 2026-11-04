import { useAtomValue } from 'jotai'
import { useEffect } from 'react'
import { useTranslation } from 'react-i18next'

import { gameIdAtom } from '../state/location-atoms'
import { gameInfoAtom } from '../state/query-atoms'
import { useGameTranslation } from '../utils/translation'

/** Sets the title of the browser tab: the translated game title inside a game */
export function useDocumentTitle() {
  const { t } = useTranslation()
  const gameId = useAtomValue(gameIdAtom)
  const { data: gameInfo } = useAtomValue(gameInfoAtom)
  const { t: gameT } = useGameTranslation(
    gameId ?? '',
    gameInfo?.settings?.allowEmptyTranslations,
  )
  const title =
    gameId !== undefined && gameInfo?.title
      ? gameT(gameInfo.title)
      : t('landing.title')
  useEffect(() => {
    document.title = title
  }, [title])
}
