import { useAtomValue } from 'jotai'
import { useTranslation } from 'react-i18next'

import { WorldChat, WorldConclusionChat } from '../Chat/Chat'
import { PanelLayout } from '../components/PanelLayout'
import { WorldImage } from '../components/WorldImage'
import { Inventory } from '../Inventory/Inventory'
import {
  preloadFirstLevelEffect,
  requestLeanEffect,
} from '../state/proof-atoms'

/**
 * A world of a game at `/owner/repo/world` with its introduction, or with its
 * `conclusion` at `/owner/repo/world/conclusion` after its last level
 */
export function WorldPage({ conclusion = false }: { conclusion?: boolean }) {
  const { t } = useTranslation()
  useAtomValue(requestLeanEffect)
  useAtomValue(preloadFirstLevelEffect)
  return (
    <PanelLayout
      leftTitle={conclusion ? t('game.conclusion') : t('game.introduction')}
      rightTitle={t('game.inventory')}
      left={conclusion ? <WorldConclusionChat /> : <WorldChat />}
      center={
        <div className="relative h-full bg-(--section-bg)">
          <WorldImage />
        </div>
      }
      right={<Inventory />}
    />
  )
}
