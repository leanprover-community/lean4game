import * as React from 'react'
import { useEffect } from 'react'

import '@fontsource/roboto/300.css'
import '@fontsource/roboto/400.css'
import '@fontsource/roboto/500.css'
import '@fontsource/roboto/700.css'
import '../../css/level.css'
import { useGameTranslation } from '../../utils/translation'
import { useAtom } from 'jotai'
import { gameIdAtom, levelIdAtom, worldIdAtom } from '../../store/location-atoms'
import { gameInfoAtom } from '../../store/query-atoms'
import { PlayableLevel } from './PlayableLevel'
import { IntroLevel } from './IntroLevel'

export default function Level() {
  const { t: gT, i18n } = useGameTranslation()
  const [gameId] = useAtom(gameIdAtom)
  const [worldId] = useAtom(worldIdAtom)
  const [levelId] = useAtom(levelIdAtom)
  const [{ data: gameInfo }] = useAtom(gameInfoAtom)

  // Load the namespace of the game
  i18n.loadNamespaces(gameId ?? "").catch(err => {
    console.warn(`translations for ${gameId} do not exist.`)
  })

  // set the window title
  useEffect(() => {
    if (gameInfo?.title) {
      window.document.title = gT(gameInfo.title)
    }
  }, [gameInfo?.title, i18n.language])

  return (
    levelId == 0 ?
      <IntroLevel /> :
      <PlayableLevel key={`${worldId}/${levelId}`} />
    )
}
