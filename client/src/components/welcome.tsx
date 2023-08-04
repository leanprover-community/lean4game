import * as React from 'react'
import { useState, useEffect } from 'react'
import { useSelector } from 'react-redux'
import Split from 'react-split'
import { Box, Typography, CircularProgress } from '@mui/material'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faGlobe, faBook, faArrowRight, faArrowLeft } from '@fortawesome/free-solid-svg-icons'

import { GameIdContext } from '../app'
import { useAppDispatch } from '../hooks'
import { changedOpenedIntro, selectOpenedIntro } from '../state/progress'
import { useGetGameInfoQuery } from '../state/api'
import { Button } from './button'
import { MobileContext } from './infoview/context'
import { InventoryPanel } from './inventory'
import Markdown from './markdown'
import {PrivacyPolicy} from './privacy_policy'
import { WelcomeMenu, WorldTreePanel } from './world_tree'

import './welcome.css'

/** navigation to switch between pages on mobile */
function MobileNav({pageNumber, setPageNumber}:
  { pageNumber: number,
    setPageNumber: any}) {
  const gameId = React.useContext(GameIdContext)
  const dispatch = useAppDispatch()

  let prevText = {0 : null, 1: "Intro", 2: "Game"}[pageNumber]
  let prevIcon = {0 : faGlobe, 1: null, 2: null}[pageNumber]
  let prevTitle = {
    0: "back to games selection",
    1: "back to introduction",
    2: "game tree"}[pageNumber]
  let nextText = {0 : "Game", 1: null, 2: null}[pageNumber]
  let nextIcon = {0 : null, 1: faBook, 2: null}[pageNumber]
  let nextTitle = {
    0: "game tree",
    1: "inventory",
    2: null}[pageNumber]

  return <div className="mobile-nav">
    {(prevText || prevTitle || prevIcon) &&
      <Button className="btn btn-previous" to={pageNumber == 0 ? "/" : ""} title={prevTitle}
          onClick={() => {pageNumber == 0 ? null : setPageNumber(pageNumber - 1)}}>

        <FontAwesomeIcon icon={faArrowLeft} />
        {prevIcon && <FontAwesomeIcon icon={prevIcon} />}
        {prevText && `${prevText}`}
      </Button>
    }
    {(nextText || nextTitle || nextIcon) &&
      <Button className="btn btn-next" to=""
          title={nextTitle} onClick={() => {
            console.log(`page number: ${pageNumber}`)
            setPageNumber(pageNumber+1);
            dispatch(changedOpenedIntro({game: gameId, openedIntro: true}))}}>
        {nextText && `${nextText}`}
        {nextIcon && <FontAwesomeIcon icon={nextIcon} />}
        <FontAwesomeIcon icon={faArrowRight}/>
      </Button>
    }
  </div>
}

/** The panel showing the game's introduction text */
function IntroductionPanel({introduction}: { introduction: string}) {
  const {mobile} = React.useContext(MobileContext)
  return <div className="column">
    <Typography variant="body1" component="div" className="welcome-text">
      {!mobile && <WelcomeMenu />}
      <Markdown>{introduction}</Markdown>
    </Typography>
  </div>
}

/** main page of the game showing amoung others the tree of worlds/levels */
function Welcome() {
  const gameId = React.useContext(GameIdContext)
  const {mobile} = React.useContext(MobileContext)
  const gameInfo = useGetGameInfoQuery({game: gameId})
  // On mobile, the intro page should only be shown the first time
  const openedIntro = useSelector(selectOpenedIntro(gameId))
  // On mobile, there are multiple pages to switch between
  const [pageNumber, setPageNumber] = useState(openedIntro ? 1 : 0)

  // set the window title
  useEffect(() => {
    if (gameInfo.data?.title) {
      window.document.title = gameInfo.data.title
    }
  }, [gameInfo.data?.title])

  return <div className="app-content">
  { gameInfo.isLoading?
    <Box display="flex" alignItems="center" justifyContent="center" sx={{ height: "calc(100vh - 64px)" }}>
      <CircularProgress />
    </Box>
    : mobile ?
      <>
        <MobileNav pageNumber={pageNumber} setPageNumber={setPageNumber} />
        {(pageNumber == 0 ?
          <IntroductionPanel introduction={gameInfo.data?.introduction} />
        : pageNumber == 1 ?
          <WorldTreePanel worlds={gameInfo.data?.worlds} worldSize={gameInfo.data?.worldSize} />
        :
          <InventoryPanel />
        )}
      </>
    :
      <Split className="welcome" minSize={0} snapOffset={200}  sizes={[40, 35, 25]}>
        <IntroductionPanel introduction={gameInfo.data?.introduction} />
        <WorldTreePanel worlds={gameInfo.data?.worlds} worldSize={gameInfo.data?.worldSize} />
        <InventoryPanel />
      </Split>
  }
  <PrivacyPolicy />
  </div>
}

export default Welcome
