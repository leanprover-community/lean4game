import * as React from 'react'
import { useSelector } from 'react-redux'
import { GameIdContext } from '../../app'
import { useAppDispatch } from '../../hooks'
import { deleteProgress, selectProgress } from '../../state/progress'
import { downloadFile } from '../world_tree'
import { Button } from '../button'
import { Trans, useTranslation } from 'react-i18next'
import { useContext } from 'react'
import { PopupContext } from './popup'

/** download the current progress (i.e. what's saved in the browser store) */
export function downloadProgress(gameId: string) {
  const gameProgress = useSelector(selectProgress(gameId))

  // ev.preventDefault()
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
export function ErasePopup () {
  let { t } = useTranslation()
  const {gameId} = React.useContext(GameIdContext)
  const gameProgress = useSelector(selectProgress(gameId))
  const dispatch = useAppDispatch()
  const { setPopupContent } = useContext(PopupContext)

  const eraseProgress = () => {
    dispatch(deleteProgress({game: gameId}))
    setPopupContent(null)
  }

  const downloadAndErase = (ev) => {
    downloadProgress(gameId)
    eraseProgress()
  }

  return <>
    <h2>{t("Delete Progress?")}</h2>
    <Trans>
      <p>Do you want to delete your saved progress irreversibly?</p>
      <p>
        (This deletes your proofs and your collected inventory.
        Saves from other games are not deleted.)
      </p>
    </Trans>
    <Button onClick={eraseProgress} to="">{t("Delete")}</Button>
    <Button onClick={downloadAndErase} to="">{t("Download & Delete")}</Button>
    <Button onClick={() => {setPopupContent(null)}} to="">{t("Cancel")}</Button>
  </>
}
