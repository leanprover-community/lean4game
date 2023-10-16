import * as React from 'react'
import { useState, useEffect } from 'react'
import { useSelector } from 'react-redux'
import Split from 'react-split'
import { Box, Typography, CircularProgress } from '@mui/material'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faGlobe, faArrowRight, faArrowLeft } from '@fortawesome/free-solid-svg-icons'

import { GameIdContext } from '../app'
import { useAppDispatch } from '../hooks'
import { GameProgressState, changedOpenedIntro, deleteProgress, loadProgress, selectOpenedIntro, selectProgress } from '../state/progress'
import { useGetGameInfoQuery, useLoadInventoryOverviewQuery } from '../state/api'
import { Button } from './button'
import { MobileContext } from './infoview/context'
import { InventoryPanel } from './inventory'
import Markdown from './markdown'
import { PrivacyPolicyPopup } from './privacy_policy'
import { RulesHelpPopup } from './popup/rules_help'
import { WorldTreePanel, downloadFile } from './world_tree'

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

export function InfoPopup ({info, handleClose}: {info: string, handleClose: () => void}) {
  return <div className="modal-wrapper">
  <div className="modal-backdrop" onClick={handleClose} />
  <div className="modal">
    <div className="codicon codicon-close modal-close" onClick={handleClose}></div>
    <Typography variant="body1" component="div" className="welcome-text">
      <Markdown>{info}</Markdown>
    </Typography>
  </div>
</div>
}


function ErasePopup ({handleClose}) {
  const gameId = React.useContext(GameIdContext)
  const gameProgress = useSelector(selectProgress(gameId))
  const dispatch = useAppDispatch()

  /** Download the current progress (i.e. what's saved in the browser store) */
  const downloadProgress = (e) => {
    e.preventDefault()
    downloadFile({
      data: JSON.stringify(gameProgress, null, 2),
      fileName: `lean4game-${gameId}-${new Date().toLocaleDateString()}.json`,
      fileType: 'text/json',
    })
  }

  const eraseProgress = () => {
    dispatch(deleteProgress({game: gameId}))
    handleClose()
  }

  const downloadAndErase = (e) => {
    downloadProgress(e)
    eraseProgress()
  }

  return <div className="modal-wrapper">
  <div className="modal-backdrop" onClick={handleClose} />
  <div className="modal">
    <div className="codicon codicon-close modal-close" onClick={handleClose}></div>
    <h2>Delete Progress?</h2>

    <p>Do you want to delete your saved progress irreversibly?</p>
    <p>
      (This deletes your proofs and your collected inventory.
      Saves from other games are not deleted.)
    </p>

    <Button onClick={eraseProgress} to="">Delete</Button>
    <Button onClick={downloadAndErase} to="">Download & Delete</Button>
    <Button onClick={handleClose} to="">Cancel</Button>
  </div>
</div>
}

function UploadPopup ({handleClose}) {
  const [file, setFile] = React.useState<File>();
  const gameId = React.useContext(GameIdContext)
  const gameProgress = useSelector(selectProgress(gameId))
  const dispatch = useAppDispatch()

  const handleFileChange = (e) => {
    if (e.target.files) {
      setFile(e.target.files[0])
    }
  }

  /** Upload progress from a  */
  const uploadProgress = (e) => {
    if (!file) {return}
    const fileReader = new FileReader()
    fileReader.readAsText(file, "UTF-8")
    fileReader.onload = (e) => {
      const data = JSON.parse(e.target.result.toString()) as GameProgressState
      console.debug("Json Data", data)
      dispatch(loadProgress({game: gameId, data: data}))
    }
    handleClose()
  }

  /** Download the current progress (i.e. what's saved in the browser store) */
  const downloadProgress = (e) => {
    e.preventDefault()
    downloadFile({
      data: JSON.stringify(gameProgress, null, 2),
      fileName: `lean4game-${gameId}-${new Date().toLocaleDateString()}.json`,
      fileType: 'text/json',
    })
  }


  return <div className="modal-wrapper">
  <div className="modal-backdrop" onClick={handleClose} />
  <div className="modal">
    <div className="codicon codicon-close modal-close" onClick={handleClose}></div>
    <h2>Upload Saved Progress</h2>

    <p>Select a JSON file with the saved game progress to load your progress.</p>

    <p><b>Warning:</b> This will delete your current game progress!
      Consider <a className="download-link" onClick={downloadProgress} >downloading your current progress</a> first!</p>

    <input type="file" onChange={handleFileChange}/>

    <Button to="" onClick={uploadProgress}>Load selected file</Button>
  </div>
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
