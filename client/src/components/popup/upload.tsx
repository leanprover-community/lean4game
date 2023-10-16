/**
 * @fileOverview
*/
import * as React from 'react'
import { useSelector } from 'react-redux'
import { GameIdContext } from '../../app'
import { useAppDispatch } from '../../hooks'
import { GameProgressState, loadProgress, selectProgress } from '../../state/progress'
import { downloadFile } from '../world_tree'
import { Button } from '../button'

/** Pop-up that is displaying the Game Info.
 *
 * `handleClose` is the function to close it again because it's open/closed state is
 * controlled by the containing element.
 */
export function UploadPopup ({handleClose}) {
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
    <p>
      <input type="file" onChange={handleFileChange}/>
    </p>

    <Button to="" onClick={uploadProgress}>Load selected file</Button>
  </div>
</div>
}
