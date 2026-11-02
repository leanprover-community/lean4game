import { useAtomValue, useSetAtom } from 'jotai'
import { Trans, useTranslation } from 'react-i18next'

import { Button } from '../components/Button'
import { Popup } from '../components/Popup'
import { gameIdAtom, routeAtom } from '../state/location-atoms'
import {
  downloadProgressAtom,
  levelProgressAtom,
  progressAtom,
  worldProgressAtom,
} from '../state/progress-atoms'

/**
 * Asks before deleting the progress of the current game. In a world or a level, it also
 * offers to delete only their progress.
 */
export function ErasePopup({
  open,
  onClose,
}: {
  open: boolean
  onClose: () => void
}) {
  const { t } = useTranslation()
  const route = useAtomValue(routeAtom)
  const gameId = useAtomValue(gameIdAtom)
  const setGameId = useSetAtom(gameIdAtom)
  const setProgress = useSetAtom(progressAtom)
  const setWorldProgress = useSetAtom(worldProgressAtom)
  const setLevelProgress = useSetAtom(levelProgressAtom)
  const downloadProgress = useSetAtom(downloadProgressAtom)

  const eraseLevel = () => {
    setLevelProgress(null)
    onClose()
  }
  const eraseWorld = () => {
    setWorldProgress(null)
    onClose()
  }
  // the worlds and levels are locked again, so back to the overview
  const eraseAll = () => {
    setProgress(null)
    onClose()
    if (gameId) setGameId(gameId)
  }

  return (
    <Popup open={open} onClose={onClose} title={t('progress.eraseTitle')}>
      <p>{t('progress.eraseQuestion')}</p>
      <div className="my-4 flex flex-wrap gap-2">
        {route.page === 'level' && (
          <Button onClick={eraseLevel}>{t('progress.deleteLevel')}</Button>
        )}
        {'world' in route && (
          <Button onClick={eraseWorld}>{t('progress.deleteWorld')}</Button>
        )}
        <Button onClick={eraseAll}>{t('progress.deleteAll')}</Button>
      </div>
      <div>
        <Trans
          i18nKey="progress.deleteAllWarning"
          components={{ p: <p className="my-2" /> }}
        />
      </div>
      <div className="mt-4 flex flex-wrap gap-2">
        <Button
          onClick={() => {
            downloadProgress()
            eraseAll()
          }}
        >
          {t('progress.downloadAndDeleteAll')}
        </Button>
        <Button onClick={onClose}>{t('progress.cancel')}</Button>
      </div>
    </Popup>
  )
}
