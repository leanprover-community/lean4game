import { faCircleCheck } from '@fortawesome/free-solid-svg-icons'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { useAtomValue } from 'jotai'
import { useTranslation } from 'react-i18next'

import { LevelChat } from '../Chat/Chat'
import { PanelLayout } from '../components/PanelLayout'
import { Inventory } from '../Inventory/Inventory'
import { MaskMenu, SelectedMask } from '../Masks/MaskMenu'
import { mobileAtom } from '../state/preferences-atoms'
import { completedAtom } from '../state/progress-atoms'

export function LevelPage() {
  const { t } = useTranslation()
  const mobile = useAtomValue(mobileAtom)
  // stays once the level was solved, even if the proof is changed later
  const completed = useAtomValue(completedAtom)
  return (
    <PanelLayout
      leftTitle={t('game.chat')}
      rightTitle={t('game.inventory')}
      centerTitle={
        completed && (
          // the title of the bar is centered, the icon goes to the left
          <span className="block text-left">
            <span
              role="img"
              title={t('typewriter.levelSolved')}
              aria-label={t('typewriter.levelSolved')}
            >
              <FontAwesomeIcon
                icon={faCircleCheck}
                className="cursor-help text-green-600 dark:text-green-400"
              />
            </span>
          </span>
        )
      }
      left={mobile ? null : <LevelChat />}
      centerActions={<MaskMenu />}
      center={<SelectedMask />}
      right={<Inventory />}
    />
  )
}
