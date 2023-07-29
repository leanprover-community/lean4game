/**
 * @fileOverview Define the menu displayed with the tree of worlds on the welcome page
*/
import * as React from 'react'
import { useStore, useSelector } from 'react-redux';
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faDownload, faUpload, faEraser, faGlobe, faHome, faArrowLeft } from '@fortawesome/free-solid-svg-icons'

import './world_selection_menu.css'

import { Button } from './button'
import { GameIdContext } from '../app';
import { useAppDispatch, useAppSelector } from '../hooks';
import { deleteProgress, selectProgress, loadProgress, GameProgressState, selectDifficulty, changedDifficulty } from '../state/progress';
import { Slider } from '@mui/material';

/** Only to specify the types for `downloadFile` */
interface downloadFileParam {
  data: string
  fileName: string
  fileType: string
}

/** Download a file containing `data` */
const downloadFile = ({ data, fileName, fileType } : downloadFileParam) => {
  const blob = new Blob([data], { type: fileType })
  const a = document.createElement('a')
  a.download = fileName
  a.href = window.URL.createObjectURL(blob)
  const clickEvt = new MouseEvent('click', {
    view: window,
    bubbles: true,
    cancelable: true,
  })
  a.dispatchEvent(clickEvt)
  a.remove()
}

// <div><Button inverted="false" title="back to games selection" to="/">
// <FontAwesomeIcon icon={faArrowLeft} />&nbsp;<FontAwesomeIcon icon={faGlobe} />
// </Button>
// <Slider min={0} max={2}></Slider>

/** The menu that is shown next to the world selection graph */
export function WelcomeMenu() {

  return <nav className="world-selection-menu">
    <Button inverted="false" title="back to games selection" to="/">
      <FontAwesomeIcon icon={faArrowLeft} />&nbsp;<FontAwesomeIcon icon={faGlobe} />
    </Button>

  </nav>
}

/** The menu that is shown next to the world selection graph */
export function WorldSelectionMenu() {
  const [file, setFile] = React.useState<File>();

  const gameId = React.useContext(GameIdContext)
  const store = useStore()
  const difficulty = useSelector(selectDifficulty(gameId))


  /* state variables to toggle the pop-up menus */
  const [eraseMenu, setEraseMenu] = React.useState(false);
  const openEraseMenu = () => setEraseMenu(true);
  const closeEraseMenu = () => setEraseMenu(false);
  const [uploadMenu, setUploadMenu] = React.useState(false);
  const openUploadMenu = () => setUploadMenu(true);
  const closeUploadMenu = () => setUploadMenu(false);

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
    closeUploadMenu()
  }

  const eraseProgress = () => {
    dispatch(deleteProgress({game: gameId}))
    closeEraseMenu()
  }

  const downloadAndErase = (e) => {
    downloadProgress(e)
    eraseProgress()
  }

  function label(x : number) {
    return x == 0 ? 'playground' : x == 1 ? 'explorer' : 'regular'
  }

  return <nav className="world-selection-menu">
    <Button onClick={downloadProgress} title="Download game progress" to=""><FontAwesomeIcon icon={faDownload} /></Button>
    <Button title="Load game progress from JSON" onClick={openUploadMenu} to=""><FontAwesomeIcon icon={faUpload} /></Button>
    <Button title="Clear game progress" to="" onClick={openEraseMenu}><FontAwesomeIcon icon={faEraser} /></Button>
    <div className="slider-wrap">
      <span className="difficulty-label">difficulty:</span>
      <Slider
        title="Difficulties:&#10;- regular: 🔐 levels, 🔐 tactics&#10;- explorer: 🔓 levels, 🔐 tactics&#10;- playground: 🔓 levels, 🔓 tactics"
        min={0} max={2}
        aria-label="Mode"
        defaultValue={difficulty}
        marks={[
          {value: 0, label: label(0)},
          {value: 1, label: label(1)},
          {value: 2, label: label(2)}
        ]}
        valueLabelFormat={label}
        getAriaValueText={label}
        valueLabelDisplay="auto"
        onChange={(ev, val: number) => {
          dispatch(changedDifficulty({game: gameId, difficulty: val}))
        }}
        ></Slider>

    </div>
    {eraseMenu?
      <div className="modal-wrapper">
        <div className="modal-backdrop" onClick={closeEraseMenu} />
        <div className="modal">
          <div className="codicon codicon-close modal-close" onClick={closeEraseMenu}></div>
          <h2>Delete Progress?</h2>

          <p>Do you want to delete your saved progress irreversibly?</p>
          <p>
            (This deletes your proofs and your collected inventory.
            Saves from other games are not deleted.)
          </p>

          <Button onClick={eraseProgress} to="">Delete</Button>
          <Button onClick={downloadAndErase} to="">Download & Delete</Button>
          <Button onClick={closeEraseMenu} to="">Cancel</Button>
        </div>
      </div> : null}
    {uploadMenu ?
      <div className="modal-wrapper">
        <div className="modal-backdrop" onClick={closeUploadMenu} />
        <div className="modal">
          <div className="codicon codicon-close modal-close" onClick={closeUploadMenu}></div>
          <h2>Upload Saved Progress</h2>

          <p>Select a JSON file with the saved game progress to load your progress.</p>

          <p><b>Warning:</b> This will delete your current game progress!
            Consider <a className="download-link" onClick={downloadProgress} >downloading your current progress</a> first!</p>

          <input type="file" onChange={handleFileChange}/>

          <Button to="" onClick={uploadProgress}>Load selected file</Button>
        </div>
      </div> : null}
  </nav>
}

export default WorldSelectionMenu
