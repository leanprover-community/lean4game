import * as React from 'react'
import { useStore, useSelector } from 'react-redux';
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faDownload, faUpload, faEraser } from '@fortawesome/free-solid-svg-icons'

import { Button } from './button'
import { GameIdContext } from '../app';
import { useAppDispatch, useAppSelector } from '../hooks';
import { deleteProgress, selectProgress, loadProgress, GameProgressState } from '../state/progress';

const downloadFile = ({ data, fileName, fileType }) => {
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

function GameMenu() {

  const [file, setFile] = React.useState<File>();

  const gameId = React.useContext(GameIdContext)
  const store = useStore()

  const [eraseMenu, setEraseMenu] = React.useState(false);
  const openEraseMenu = () => setEraseMenu(true);
  const closeEraseMenu = () => setEraseMenu(false);

  const [uploadMenu, setUploadMenu] = React.useState(false);
  const openUploadMenu = () => setUploadMenu(true);
  const closeUploadMenu = () => setUploadMenu(false);

  const gameProgress = useSelector(selectProgress(gameId))

  const dispatch = useAppDispatch()

  const downloadProgress = (e) => {
    e.preventDefault()
    downloadFile({
      data: JSON.stringify(gameProgress),
      fileName: `lean4game-${gameId}-${new Date().toLocaleDateString()}.json`,
      fileType: 'text/json',
    })
  };

  const handleFileChange = (e) => {
    if (e.target.files) {
      setFile(e.target.files[0]);
    }

  };

  const uploadProgress = (e) => {
    if (!file) {
      return;
    }

    const fileReader = new FileReader();
    fileReader.readAsText(file, "UTF-8");
    fileReader.onload = (e) => {
      const data = JSON.parse(e.target.result.toString()) as GameProgressState;
      console.debug("Json Data", data);

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

  return <nav className="game-menu">
    <Button onClick={downloadProgress} title="Download game progress" to=""><FontAwesomeIcon icon={faDownload} /></Button>
    <Button title="Load game progress from JSON" onClick={openUploadMenu} to=""><FontAwesomeIcon icon={faUpload} /></Button>
    <Button title="Clear game progress" to="" onClick={openEraseMenu}><FontAwesomeIcon icon={faEraser} /></Button>

    {eraseMenu?
      <div className="modal-wrapper">
      <div className="modal-backdrop" onClick={closeEraseMenu} />
      <div className="modal">
        <div className="codicon codicon-close modal-close" onClick={closeEraseMenu}></div>
        <h2>Delete Progress?</h2>

        <p>Do you want to delete your saved progress irreversibly?</p>
        <p>(This only affects your saved proofs, no levels are ever locked.
          Saves from other games are not deleted.)</p>

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

export default GameMenu
