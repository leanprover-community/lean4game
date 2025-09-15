/**
 * @fileOverview
*/
import * as React from 'react'
import { useSelector } from 'react-redux'
import { GameIdContext } from '../../app'
import { useAppDispatch } from '../../hooks'
import { deleteLevelProgress, deleteProgress, deleteWorldProgress, selectProgress } from '../../state/progress'
import { downloadFile } from '../world_tree'
import { Button } from '../button'
import { Trans, useTranslation } from 'react-i18next'
import { useContext } from 'react'
import { useAtom } from 'jotai'
import { popupAtom } from '../../store/popup-atoms'
import { WorldLevelIdContext } from '../infoview/context'

/** download the current progress (i.e. what's saved in the browser store) */
export function downloadProgress(gameId: string, gameProgress: any, ev: React.MouseEvent) {
  ev.preventDefault()
  downloadFile({
    data: JSON.stringify(gameProgress, null, 2),
    fileName: `lean4game-${gameId}-${new Date().toLocaleDateString()}.json`,
    fileType: 'text/json',
  })
}

// /** Pop-up to delete game progress.
//  *
//  * `handleClose` is the function to close it again because it's open/closed state is
//  * controlled by the containing element.
//  */
// export function ErasePopup ({handleClose}) {
//   let { t } = useTranslation()
//   const gameId = React.useContext(GameIdContext)
//   const gameProgress = useSelector(selectProgress(gameId))
//   const dispatch = useAppDispatch()

//   const eraseProgress = () => {
//     dispatch(deleteProgress({game: gameId}))
//     handleClose()
//   }

//   const downloadAndErase = (ev) => {
//     downloadProgress(gameId, gameProgress, ev)
//     eraseProgress()
//   }

//   return <div className="modal-wrapper">
//   <div className="modal-backdrop" onClick={handleClose} />
//   <div className="modal">
//     <div className="codicon codicon-close modal-close" onClick={handleClose}></div>
//     <h2>{t("Delete Progress?")}</h2>
//     <Trans>
//       <p>Do you want to delete your saved progress irreversibly?</p>
//       <p>
//         (This deletes your proofs and your collected inventory.
//         Saves from other games are not deleted.)
//       </p>
//     </Trans>
//     <Button onClick={eraseProgress} to="">{t("Delete")}</Button>
//     <Button onClick={downloadAndErase} to="">{t("Download & Delete")}</Button>
//     <Button onClick={handleClose} to="">{t("Cancel")}</Button>
//   </div>
// </div>
// }

export function ErasePopup () {
  let { t } = useTranslation()
  const gameId = useContext(GameIdContext)
   const {worldId, levelId} = React.useContext(WorldLevelIdContext)
  // const { setPage } = useContext(PageContext)
  const gameProgress = useSelector(selectProgress(gameId))
  const dispatch = useAppDispatch()
  const [, setPopup] = useAtom(popupAtom)

  const eraseProgress = (ev) => {
    dispatch(deleteProgress({game: gameId}))
    setPopup(null)
    // setPage(0) // TODO: fix me
    // ev.preventDefault() // TODO: this is a hack to prevent the buttons below from opening a link
  }

  function eraseLevel (ev) {
    dispatch(deleteLevelProgress({game: gameId, world: worldId, level: levelId}))
    setPopup(null)
    ev.preventDefault()
  }

  function eraseWorld (ev) {
    dispatch(deleteWorldProgress({game: gameId, world: worldId}))
    setPopup(null)
    ev.preventDefault()
  }

  const downloadAndErase = (ev) => {
    downloadProgress(gameId, gameProgress, ev)
    eraseProgress(ev)
  }

  return <>
    <h2>{t("Delete Progress?")}</h2>
    <Trans>
      <p>Do you want to delete your saved progress irreversibly?</p>
    </Trans>
    <div className='settings-buttons'>
      <Button onClick={levelId && eraseLevel} to="" disabled={!levelId} >{t("Delete this Level")}</Button>
      <Button onClick={worldId && eraseWorld} to="" disabled={!worldId} >{t("Delete this World")}</Button>
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
      <Button onClick={(ev) => {setPopup(null); ev.preventDefault()}} to="">{t("Cancel")}</Button>
    </div>
  </>
}
