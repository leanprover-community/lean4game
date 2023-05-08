import * as React from 'react'
import { Button } from './Button'
import { GameIdContext } from '../App';
import { useStore } from 'react-redux';
import { useAppDispatch, useAppSelector } from '../hooks';

import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faDownload, faUpload, faEraser } from '@fortawesome/free-solid-svg-icons'

import { deleteProgress } from '../state/progress';

function GameMenu() {

  const gameId = React.useContext(GameIdContext)
  const store = useStore()

  const [eraseMenu, setEraseMenu] = React.useState(false);
  const openEraseMenu = () => setEraseMenu(true);
  const closeEraseMenu = () => setEraseMenu(false);

  const dispatch = useAppDispatch()

  const downloadProgress = () => {};
  // const uploadProgress = () => {};

  const eraseProgress = () => {
    dispatch(deleteProgress({game: gameId}))
    closeEraseMenu()
  }

  const downloadAndErase = () => {
    downloadProgress ()
    eraseProgress()
  }

  return <nav className="game-menu">
    <Button disabled={true} onClick={downloadProgress} title="Download game progress" to=""><FontAwesomeIcon icon={faDownload} /></Button>
    <Button disabled={true} title="Load game progress from JSON" to=""><FontAwesomeIcon icon={faUpload} /></Button>
    <Button title="Clear game progress" to="" onClick={openEraseMenu}><FontAwesomeIcon icon={faEraser} /></Button>

    {eraseMenu?
      <div className="modal-wrapper">
      <div className="modal-backdrop" onClick={closeEraseMenu} />
      <div className="modal">
        <div className="codicon codicon-close modal-close" onClick={closeEraseMenu}></div>
        <h2>Delete Progress?</h2>

        <p>Do you want to delete your saved state irreversibly?</p>
        <p>(This only affects your saved proofs, no levels are ever locked.
          Saves from other games are not deleted.)</p>

        <Button onClick={eraseProgress} to="">Delete</Button>
        <Button disabled={true} onClick={downloadAndErase} to="">Download & Delete</Button>
        <Button onClick={closeEraseMenu} to="">Cancel</Button>
      </div>
    </div> : null}
  </nav>
}

export default GameMenu
