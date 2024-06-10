import * as React from 'react'
import { useSelector } from 'react-redux'
import { useAppDispatch } from '../../hooks'
import { deleteProgress, selectProgress } from '../../state/progress'
import { downloadFile } from '../world_tree'
import { Button } from '../button'
import { Trans, useTranslation } from 'react-i18next'
import { useContext } from 'react'
import { PopupContext } from './popup'
import { GameIdContext, PageContext } from '../../state/context'

/** download the current progress (i.e. what's saved in the browser store) */
export function downloadProgress(gameId: string, gameProgress) {

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
  const {setPage} = useContext(PageContext)
  const gameProgress = useSelector(selectProgress(gameId))
  const dispatch = useAppDispatch()
  const { setPopupContent } = useContext(PopupContext)

  const eraseProgress = (ev) => {
    dispatch(deleteProgress({game: gameId}))
    setPopupContent(null)
    setPage(0)
    // ev.preventDefault() // TODO: this is a hack to prevent the buttons below from opening a link
  }

  const downloadAndErase = (ev) => {
    downloadProgress(gameId, gameProgress)
    eraseProgress(ev)
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
    <Button onClick={eraseProgress} to={`/${gameId}/`}>{t("Delete")}</Button>
    <Button onClick={downloadAndErase} to={`/${gameId}/`}>{t("Download & Delete")}</Button>
    <Button onClick={(ev) => {setPopupContent(null); ev.preventDefault()}} to="">{t("Cancel")}</Button>
  </>
}
