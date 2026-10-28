import { useTranslation } from 'react-i18next'

import { PanelLayout } from '../components/PanelLayout'
import { WorldImage } from '../components/WorldImage'

/** A world of a game at `/owner/repo/world`. TODO: the side panels are still empty */
export function WorldPage() {
  const { t } = useTranslation()
  return (
    <PanelLayout
      leftTitle={t('game.introduction')}
      rightTitle={t('game.inventory')}
      left={null}
      center={
        <div className="relative h-full bg-(--section-bg)">
          <WorldImage />
        </div>
      }
      right={null}
    />
  )
}
