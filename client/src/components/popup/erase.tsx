import * as React from 'react'
import { useSelector } from 'react-redux'
import { useAppDispatch } from '../../hooks'
import { deleteLevelProgress, deleteProgress, deleteWorldProgress, selectProgress } from '../../state/progress'
import { downloadFile } from '../world_tree'
import { Button } from '../utils'
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
  const { gameId, worldId, levelId } = React.useContext(GameIdContext)
  const { setPage } = useContext(PageContext)
  const gameProgress = useSelector(selectProgress(gameId))
  const dispatch = useAppDispatch()
  const { setPopupContent } = useContext(PopupContext)

  const eraseProgress = (ev) => {
    dispatch(deleteProgress({game: gameId}))
    setPopupContent(null)
    setPage(0)
    // ev.preventDefault() // TODO: this is a hack to prevent the buttons below from opening a link
  }

  function eraseLevel (ev) {
    dispatch(deleteLevelProgress({game: gameId, world: worldId, level: levelId}))
    setPopupContent(null)
    ev.preventDefault()
  }

  function eraseWorld (ev) {
    dispatch(deleteWorldProgress({game: gameId, world: worldId}))
    setPopupContent(null)
    ev.preventDefault()
  }

  const downloadAndErase = (ev) => {
    downloadProgress(gameId, gameProgress)
    eraseProgress(ev)
  }

  return <>
    <h2>{t("Delete Progress?")}</h2>
    <Trans>
      <p>Do you want to delete your saved progress irreversibly?</p>
    </Trans>
    <div className='settings-buttons'>
      { levelId ?
        <Button onClick={eraseLevel} to="">{t("Delete this Level")}</Button> : <></>
      }
      { worldId ?
        <Button onClick={eraseWorld} to="">{t("Delete this World")}</Button> : <></>
      }
      <Button onClick={eraseProgress} to={`/${gameId}/`}>{t("Delete Everything")}</Button>
    </div>
    <Trans>
      <p>
        Deleting everything will delete all your proofs and your collected inventory! It's recommended
        to download your progress first.
      </p>
      <p>
        (Saves from other games are not deleted.)
      </p>
    </Trans>
    <div className='settings-buttons'>
      <Button onClick={downloadAndErase} to={`/${gameId}/`}>{t("Download & Delete everything")}</Button>
      <Button onClick={(ev) => {setPopupContent(null); ev.preventDefault()}} to="">{t("Cancel")}</Button>
    </div>
  </>
}
