import { useTranslation } from 'react-i18next'

import { WorldChat } from '../Chat/Chat'
import { PanelLayout } from '../components/PanelLayout'
import { WorldImage } from '../components/WorldImage'
import { Inventory } from '../Inventory/Inventory'

/** A world of a game at `/owner/repo/world`. */
export function WorldPage() {
  const { t } = useTranslation()
  return (
    <PanelLayout
      leftTitle={t('game.introduction')}
      rightTitle={t('game.inventory')}
      left={<WorldChat />}
      center={
        <div className="relative h-full bg-(--section-bg)">
          <WorldImage />
        </div>
      }
      right={<Inventory />}
    />
  )
}
