/**
 * @fileOverview
*/
import * as React from 'react'
import { downloadProgress } from './erase'
import { Trans, useTranslation } from 'react-i18next'
import { popupAtom } from '../../store/popup-atoms'
import { useAtom } from 'jotai'
import { gameIdAtom } from '../../store/location-atoms'
import { progressAtom } from '../../store/progress-atoms'
import { DEFAULT_DIFFICULTY, GameProgress } from '../../store/progress-types'
import { Button } from '../button'

/** Validate and normalize uploaded JSON into a `GameProgress` object */
function validateGameProgress(text: string, gameId?: string): GameProgress | null {
  try {
    const parsed = JSON.parse(text)
    // Support both single-game `GameProgress` JSON and `{ games: { [gameId]: GameProgress } }`
    const rawProgress = (parsed?.games && gameId)
      ? (parsed.games[gameId] ?? parsed.games[gameId.toLowerCase()])
      : parsed
    if (!rawProgress || typeof rawProgress !== 'object' || (!('data' in rawProgress) && !('inventory' in rawProgress))) {
      console.error("Invalid game progress format")
      return null
    }
    return {
      ...rawProgress,
      inventory: Array.isArray(rawProgress.inventory) ? rawProgress.inventory : [],
      data: (rawProgress.data && typeof rawProgress.data === 'object') ? rawProgress.data : {},
      readIntro: Boolean(rawProgress.readIntro),
      difficulty: typeof rawProgress.difficulty === 'number' ? rawProgress.difficulty : DEFAULT_DIFFICULTY,
    }
  } catch (err) {
    console.error("Failed to parse game progress file", err)
    return null
  }
}

/** Pop-up that is displaying the Game Info.
 *
 * `handleClose` is the function to close it again because it's open/closed state is
 * controlled by the containing element.
 */
export function UploadPopup () {
  let { t } = useTranslation()

  const [file, setFile] = React.useState<File>();
  const [gameId] = useAtom(gameIdAtom)
  const [gameProgress, setProgress] = useAtom(progressAtom)

  const [, setPopup] = useAtom(popupAtom)

  const handleFileChange = (e: any) => {
    if (e.target.files) {
      setFile(e.target.files[0])
    }
  }

  /** Upload progress from a file */
  const uploadProgress = (ev: React.MouseEvent) => {
    ev.preventDefault()
    if (!file) {return}
    const fileReader = new FileReader()
    fileReader.readAsText(file, "UTF-8")
    fileReader.onload = (e: any) => {
      const data = validateGameProgress(e.target.result.toString(), gameId)
      if (data) {
        console.debug("Json Data", data)
        setProgress(data)
        // Close the popup only after the async FileReader finishes updating progress
        setPopup(null)
      }
    }
  }

  /** Download the current progress (i.e. what's saved in the browser store) */
  const handleDownloadProgress = (e: React.MouseEvent<HTMLAnchorElement, globalThis.MouseEvent>) => {
    e.preventDefault()
    if (gameId && gameProgress) {
      downloadProgress(gameId, gameProgress)
    }
  }


  return <>
    <h2>{t("Upload Saved Progress")}</h2>
    <Trans>
      <p>Select a JSON file with the saved game progress to load your progress.</p>

      <p><b>Warning:</b> This will delete your current game progress!
        Consider <a className="download-link" onClick={(ev) => handleDownloadProgress(ev)} >downloading your current progress</a> first!
      </p>
    </Trans>
    <p>
      <input type="file" onChange={handleFileChange}/>
    </p>

    <Button onClick={(ev) => uploadProgress(ev)} disabled={!file}>{t("Load selected file")}</Button>
  </>
}
