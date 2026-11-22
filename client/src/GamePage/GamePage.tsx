import { lazy, Suspense } from 'react'
import { useTranslation } from 'react-i18next'

import { GameChat } from '../Chat/Chat'
import { PanelLayout } from '../components/PanelLayout'
import { Spinner } from '../components/Spinner'
import { Inventory } from '../Inventory/Inventory'

// lazy loaded so that cytoscape and klay are not part of the index bundle
const WorldTree = lazy(() =>
  import('./WorldTree').then(m => ({ default: m.WorldTree })),
)

/** The overview of a game at `/g/owner/repo`, with its world tree. */
export function GamePage() {
  const { t } = useTranslation()
  return (
    <PanelLayout
      leftTitle={t('game.introduction')}
      rightTitle={t('game.inventory')}
      left={<GameChat />}
      center={
        <Suspense fallback={<Spinner />}>
          <WorldTree />
        </Suspense>
      }
      right={<Inventory />}
    />
  )
}
