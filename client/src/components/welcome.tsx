import * as React from 'react'
import { useState, useEffect } from 'react'
import Split from 'react-split'
import { Box, CircularProgress } from '@mui/material'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faGlobe, faArrowRight, faArrowLeft } from '@fortawesome/free-solid-svg-icons'

import { GameIdContext } from '../app'
import { useAppDispatch } from '../hooks'
import { changedOpenedIntro } from '../state/progress'
import { useGetGameInfoQuery, useLoadInventoryOverviewQuery } from '../state/api'
import { Button } from './button'
import { MobileContext } from './infoview/context'
import { InventoryPanel } from './inventory'
import { ErasePopup } from './popup/erase'
import { InfoPopup } from './popup/game_info'
import { PrivacyPolicyPopup } from './popup/privacy_policy'
import { RulesHelpPopup } from './popup/rules_help'
import { UploadPopup } from './popup/upload'
import { WorldTreePanel } from './world_tree'

import './welcome.css'
import { WelcomeAppBar } from './app_bar'
import { Hint } from './hints'


/** The panel showing the game's introduction text */
function IntroductionPanel({introduction}: {introduction: string}) {
  const {mobile, setPageNumber} = React.useContext(MobileContext)
  const gameId = React.useContext(GameIdContext)
  const dispatch = useAppDispatch()

  // TODO: I left the setup for splitting up the introduction in place, but if it's not needed
  // then this can be simplified.

  // let text: Array<string> = introduction.split(/\n(\s*\n)+/)
  let text: Array<string> = introduction ? [introduction] : []

  return <div className="column chat-panel">
    <div className="chat">
      {text?.map(((t, i) =>
        t.trim() ?
          <Hint key={`intro-p-${i}`}
            hint={{text: t, hidden: false}}
            step={0} selected={null} toggleSelection={undefined} />
        : <></>
      ))}
    </div>
    {/* <Typography variant="body1" component="div" className="welcome-text">
          <h1>{title}</h1>
          <Markdown>{introduction}</Markdown>
        </Typography>
    */}
    {mobile &&
      <div className="button-row">
        <Button className="btn" to=""
          title="" onClick={() => {
            setPageNumber(1);
            dispatch(changedOpenedIntro({game: gameId, openedIntro: true}))
          }}>
          Start&nbsp;<FontAwesomeIcon icon={faArrowRight}/>
        </Button>
      </div>
    }
  </div>
}

/** main page of the game showing amoung others the tree of worlds/levels */
function Welcome() {
  const gameId = React.useContext(GameIdContext)
  const {mobile, pageNumber, setPageNumber} = React.useContext(MobileContext)
  const gameInfo = useGetGameInfoQuery({game: gameId})
  const inventory = useLoadInventoryOverviewQuery({game: gameId})

  // impressum pop-up
  const [impressum, setImpressum] = React.useState(false)
  const [rulesHelp, setRulesHelp] = React.useState(false)

  function closeImpressum() {setImpressum(false)}
  function toggleImpressum() {setImpressum(!impressum)}
  function closeRulesHelp() {setRulesHelp(false)}

  const [info, setInfo] = React.useState(false)
  function closeInfo() {setInfo(false)}
  function toggleInfo() {setInfo(!impressum)}


  /* state variables to toggle the pop-up menus */
  const [eraseMenu, setEraseMenu] = React.useState(false);
  const openEraseMenu = () => setEraseMenu(true);
  const closeEraseMenu = () => setEraseMenu(false);
  const [uploadMenu, setUploadMenu] = React.useState(false);
  const openUploadMenu = () => setUploadMenu(true);
  const closeUploadMenu = () => setUploadMenu(false);


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
    <WelcomeAppBar gameInfo={gameInfo.data} toggleImpressum={toggleImpressum} openEraseMenu={openEraseMenu}
      openUploadMenu={openUploadMenu} toggleInfo={toggleInfo} />
    <div className="app-content">
      { mobile ?
          <div className="welcome mobile">
            {(pageNumber == 0 ?
              <IntroductionPanel introduction={gameInfo.data?.introduction} />
            : pageNumber == 1 ?
              <WorldTreePanel worlds={gameInfo.data?.worlds} worldSize={gameInfo.data?.worldSize} rulesHelp={rulesHelp} setRulesHelp={setRulesHelp} />
            :
              <InventoryPanel levelInfo={inventory?.data} />
            )}
          </div>
        :
          <Split className="welcome" minSize={0} snapOffset={200}  sizes={[25, 50, 25]}>
            <IntroductionPanel introduction={gameInfo.data?.introduction} />
            <WorldTreePanel worlds={gameInfo.data?.worlds} worldSize={gameInfo.data?.worldSize} rulesHelp={rulesHelp} setRulesHelp={setRulesHelp} />
            <InventoryPanel levelInfo={inventory?.data} />
          </Split>
      }
    </div>
    {impressum ? <PrivacyPolicyPopup handleClose={closeImpressum} /> : null}
    {rulesHelp ? <RulesHelpPopup handleClose={closeRulesHelp} /> : null}
    {eraseMenu? <ErasePopup handleClose={closeEraseMenu}/> : null}
    {uploadMenu? <UploadPopup handleClose={closeUploadMenu}/> : null}
    {info ? <InfoPopup info={gameInfo.data?.info} handleClose={closeInfo}/> : null}
  </>
}

export default Welcome
