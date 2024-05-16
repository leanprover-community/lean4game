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
import { Trans, useTranslation } from 'react-i18next'
import { PopupContext } from './popup'
import { useContext } from 'react'

/** Pop-up that is displaying the Game Info.
 *
 * `handleClose` is the function to close it again because it's open/closed state is
 * controlled by the containing element.
 */
export function UploadPopup () {
  let { t } = useTranslation()

  const [file, setFile] = React.useState<File>();
  const {gameId} = React.useContext(GameIdContext)
  const gameProgress = useSelector(selectProgress(gameId))
  const dispatch = useAppDispatch()

  const { setPopupContent } = useContext(PopupContext)

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
    setPopupContent(null) // close the popup
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


  return <>
    <h2>{t("Upload Saved Progress")}</h2>
    <Trans>
      <p>Select a JSON file with the saved game progress to load your progress.</p>

      <p><b>Warning:</b> This will delete your current game progress!
        Consider <a className="download-link" onClick={downloadProgress} >downloading your current progress</a> first!
      </p>
    </Trans>
    <p>
      <input type="file" onChange={handleFileChange}/>
    </p>

    <Button to="" onClick={uploadProgress}>{t("Load selected file")}</Button>
  </>
}
