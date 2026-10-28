import { faCircleCheck } from '@fortawesome/free-solid-svg-icons'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { useAtomValue } from 'jotai'
import { useTranslation } from 'react-i18next'

import { PanelLayout } from '../components/PanelLayout'
import { completedAtom } from '../state/progress-atoms'
import { Typewriter } from '../Typewriter/Typewriter'

export function LevelPage() {
  const { t } = useTranslation()
  // stays once the level was solved, even if the proof is changed later
  const completed = useAtomValue(completedAtom)
  return (
    <PanelLayout
      leftTitle={t('game.introduction')}
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
                className="text-green-600 dark:text-green-400"
              />
            </span>
          </span>
        )
      }
      left={null}
      center={<Typewriter />}
      right={null}
    />
  )
}
