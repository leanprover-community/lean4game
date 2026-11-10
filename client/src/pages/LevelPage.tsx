import { faCircleCheck } from '@fortawesome/free-solid-svg-icons'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { useAtomValue } from 'jotai'
import { useTranslation } from 'react-i18next'

import { LevelChat } from '../Chat/Chat'
import { resetSelectedStepEffect } from '../Chat/chat-atoms'
import { PanelLayout } from '../components/PanelLayout'
import { useLeanKeepalive } from '../hooks/useLeanKeepalive'
import { Inventory } from '../Inventory/Inventory'
import { unlockLevelItemsEffect } from '../Inventory/inventory-atoms'
import { MaskMenu, SelectedMask } from '../Masks/MaskMenu'
import { mobileAtom } from '../state/preferences-atoms'
import { completedAtom } from '../state/progress-atoms'
import {
  levelCompletedEffect,
  restartInstanceEffect,
} from '../state/proof-atoms'

export function LevelPage() {
  const { t } = useTranslation()
  const mobile = useAtomValue(mobileAtom)
  // stays once the level was solved, even if the proof is changed later
  const completed = useAtomValue(completedAtom)
  // for the level independent of the mask, which only shows it
  useAtomValue(levelCompletedEffect)
  useAtomValue(unlockLevelItemsEffect)
  useAtomValue(restartInstanceEffect)
  useAtomValue(resetSelectedStepEffect)
  useLeanKeepalive()
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
