/**
 * @fileOverview
*/
import * as React from 'react'
import { useSelector } from 'react-redux'
import { GameIdContext } from '../../app'
import { useAppDispatch } from '../../hooks'
import { deleteProgress, selectProgress } from '../../state/progress'
import { downloadFile } from '../world_tree'
import { Button } from '../button'

/** download the current progress (i.e. what's saved in the browser store) */
export function downloadProgress(gameId: string, gameProgress: any, ev: React.MouseEvent) {
  ev.preventDefault()
  downloadFile({
    data: JSON.stringify(gameProgress, null, 2),
    fileName: `lean4game-${gameId}-${new Date().toLocaleDateString()}.json`,
    fileType: 'text/json',
  })
}

/** Pop-up to delete game progress.
 *
 * `handleClose` is the function to close it again because it's open/closed state is
 * controlled by the containing element.
 */
export function ErasePopup ({handleClose}) {
  const gameId = React.useContext(GameIdContext)
  const gameProgress = useSelector(selectProgress(gameId))
  const dispatch = useAppDispatch()

  const eraseProgress = () => {
    dispatch(deleteProgress({game: gameId}))
    handleClose()
  }

  const downloadAndErase = (ev) => {
    downloadProgress(gameId, gameProgress, ev)
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
