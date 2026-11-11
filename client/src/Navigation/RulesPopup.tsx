import { faLock, faLockOpen } from '@fortawesome/free-solid-svg-icons'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { useAtom } from 'jotai'
import { Trans, useTranslation } from 'react-i18next'
import { twMerge } from 'tailwind-merge'

import { Popup } from '../components/Popup'
import { difficultyAtom } from '../state/progress-atoms'

const DIFFICULTIES = [2, 1, 0] as const

/** The translation keys of the difficulties */
const LABELS = {
  0: 'rules.none',
  1: 'rules.relaxed',
  2: 'rules.regular',
} as const

/** Whether levels or tactics are locked, for the table of the rules */
function LockIcon({ locked }: { locked: boolean }) {
  const { t } = useTranslation()
  const label = locked ? t('rules.locked') : t('rules.unlocked')
  return (
    <span title={label}>
      <FontAwesomeIcon icon={locked ? faLock : faLockOpen} />
      <span className="sr-only">{label}</span>
    </span>
  )
}

/** The popup to choose the game rules (difficulty) of the current game, with an explanation */
export function RulesPopup({
  open,
  onClose,
}: {
  open: boolean
  onClose: () => void
}) {
  const { t } = useTranslation()
  const [difficulty, setDifficulty] = useAtom(difficultyAtom)

  const label = (x: number) => t(LABELS[x as 0 | 1 | 2])

  return (
    <Popup open={open} onClose={onClose} title={t('rules.gameRules')}>
      {/* the slider next to the table of what the options lock, one row per option */}
      <table className="mx-auto mb-4 text-center">
        <thead>
          <tr className="h-8">
            <th scope="col" colSpan={2}>
              <span className="sr-only">{t('rules.gameRules')}</span>
            </th>
            <th scope="col" className="px-2">
              {t('rules.levels')}
            </th>
            <th scope="col" className="px-2">
              {t('rules.tactics')}
            </th>
          </tr>
        </thead>
        <tbody>
          {DIFFICULTIES.map((x, i) => (
            <tr
              key={x}
              // the option's button covers the whole row, see below
              className={twMerge(
                'group/row relative h-8',
                x === difficulty && 'font-bold text-primary',
              )}
            >
              {i === 0 && (
                <td
                  rowSpan={DIFFICULTIES.length}
                  // above the buttons covering the rows
                  className="relative z-10 pr-3"
                >
                  <input
                    type="range"
                    min={0}
                    max={2}
                    step={1}
                    value={difficulty}
                    aria-label={t('rules.gameRules')}
                    aria-valuetext={label(difficulty)}
                    onChange={e => setDifficulty(Number(e.target.value))}
                    // vertical, with the maximum at the top. From the middle of the first row to
                    // the middle of the last one, plus the thumb, so that the thumb is in line
                    // with the option's text
                    className={twMerge(
                      // two rows of `h-8` plus the thumb of 16px
                      'block h-20 cursor-pointer accent-primary',
                      '[direction:rtl] [writing-mode:vertical-lr]',
                    )}
                  />
                </td>
              )}
              <th
                scope="row"
                className="pr-2 text-left group-has-[button:hover]/row:bg-primary/10"
              >
                <button
                  type="button"
                  tabIndex={-1}
                  className="cursor-pointer after:absolute after:inset-0"
                  onClick={() => setDifficulty(x)}
                >
                  {label(x)}
                </button>
              </th>
              <td className="group-has-[button:hover]/row:bg-primary/10">
                <LockIcon locked={x >= 2} />
              </td>
              <td className="group-has-[button:hover]/row:bg-primary/10">
                <LockIcon locked={x >= 1} />
              </td>
            </tr>
          ))}
        </tbody>
      </table>
      <div>
        <Trans
          i18nKey="rules.help"
          components={{ p: <p className="my-2" />, code: <code /> }}
        />
      </div>
    </Popup>
  )
}
