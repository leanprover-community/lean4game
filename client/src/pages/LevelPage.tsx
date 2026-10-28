import { useTranslation } from 'react-i18next'

import { PanelLayout } from '../components/PanelLayout'
import { Typewriter } from '../Typewriter/Typewriter'

export function LevelPage() {
  const { t } = useTranslation()
  return (
    <PanelLayout
      leftTitle={t('game.introduction')}
      rightTitle={t('game.inventory')}
      left={null}
      center={<Typewriter />}
      right={null}
    />
  )
}
