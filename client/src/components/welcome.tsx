import * as React from 'react'
import { useEffect } from 'react'
import Split from 'react-split'
import { Box, CircularProgress } from '@mui/material'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faArrowRight } from '@fortawesome/free-solid-svg-icons'

import { useAppDispatch, useAppSelector } from '../hooks'
import { useGetGameInfoQuery, useLoadInventoryOverviewQuery } from '../state/api'
import { Button } from './button'
import { PreferencesContext } from './infoview/context'
import { WorldTreePanel } from './world_tree'

import '../css/welcome.css'
import { WelcomeAppBar } from './app_bar'
import { Hint } from './hints'
import i18next from 'i18next'
import { useTranslation } from 'react-i18next'
import { useGameTranslation } from '../utils/translation'
import { InventoryPanel } from './inventory/inventory_panel'
import { gameIdAtom } from '../store/location-atoms'
import { useAtom } from 'jotai'
import { readGameIntroAtom } from '../store/progress-atoms'


/** the panel showing the game's introduction text */
function IntroductionPanel({introduction, setPageNumber}: {introduction: string, setPageNumber: (val: number) => void}) {
  const {mobile} = React.useContext(PreferencesContext)
  const [gameId] = useAtom(gameIdAtom)
  const [, setReadGameIntro] = useAtom(readGameIntroAtom)


  const { t : gT } = useGameTranslation()

  const dispatch = useAppDispatch()

  // TODO: I left the setup for splitting up the introduction in place, but if it's not needed
  // then this can be simplified.

  // let text: Array<string> = introduction.split(/\n(\s*\n)+/)
  let text: Array<string> = introduction ? [gT(introduction)] : []

  return <div className="column chat-panel">
    <div className="chat">
      {text?.map(((t, i) =>
        t.trim() ?
          <Hint key={`intro-p-${i}`}
            hint={{text: t, hidden: false, rawText: t, varNames: []}}
            step={0} selected={null} toggleSelection={undefined} />
        : <></>
      ))}
    </div>
    {mobile &&
      <div className="button-row">
        <Button className="btn"
          title="" onClick={() => {
            setPageNumber(1);
            setReadGameIntro(true)
          }}>
          Start&nbsp;<FontAwesomeIcon icon={faArrowRight}/>
        </Button>
      </div>
    }
  </div>
}

/** main page of the game showing among others the tree of worlds/levels */
function Welcome() {
  const [gameId] = useAtom(gameIdAtom)
  const [readGameIntro] = useAtom(readGameIntroAtom)

  // Load the namespace of the game
  i18next.loadNamespaces(gameId)

  const {mobile} = React.useContext(PreferencesContext)
  const {layout, isSavePreferences, language, setLayout, setIsSavePreferences, setLanguage} = React.useContext(PreferencesContext)

  const gameInfo = useGetGameInfoQuery({game: gameId})
  const inventory = useLoadInventoryOverviewQuery({game: gameId})

  // For mobile only
  const [pageNumber, setPageNumber] = React.useState(readGameIntro ? 1 : 0)

  // set the window title
  useEffect(() => {
    if (gameInfo.data?.title) {
      window.document.title = gameInfo.data.title
    }
  }, [gameInfo.data?.title])

  return gameInfo.isLoading ?
    <Box display="flex" alignItems="center" justifyContent="center" sx={{ height: "calc(100vh - 64px)" }}>
      <CircularProgress />
    </Box>
  : <>
    <WelcomeAppBar pageNumber={pageNumber} setPageNumber={setPageNumber} gameInfo={gameInfo.data} />
    <div className="app-content">
      { mobile ?
          <div className="welcome mobile">
            {(pageNumber == 0 ?
              <IntroductionPanel introduction={gameInfo.data?.introduction} setPageNumber={setPageNumber} />
            : pageNumber == 1 ?
              <WorldTreePanel worlds={gameInfo.data?.worlds} worldSize={gameInfo.data?.worldSize} />
            :
              <InventoryPanel levelInfo={inventory?.data} />
            )}
          </div>
        :
          <Split className="welcome" minSize={0} snapOffset={200}  sizes={[25, 50, 25]}>
            <IntroductionPanel introduction={gameInfo.data?.introduction} setPageNumber={setPageNumber} />
            <WorldTreePanel worlds={gameInfo.data?.worlds} worldSize={gameInfo.data?.worldSize} />
            <InventoryPanel levelInfo={inventory?.data} />
          </Split>
      }
    </div>
  </>
}

export default Welcome
