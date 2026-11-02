import { useTranslation } from 'react-i18next'

import { GameChat } from '../Chat/Chat'
import { PanelLayout } from '../components/PanelLayout'
import { Inventory } from '../Inventory/Inventory'
import { WorldTree } from './WorldTree'

/** The overview of a game at `/g/owner/repo`, with its world tree. */
export function GamePage() {
  const { t } = useTranslation()
  return (
    <PanelLayout
      leftTitle={t('game.introduction')}
      rightTitle={t('game.inventory')}
      left={<GameChat />}
      center={<WorldTree />}
      right={<Inventory />}
    />
  )
}
