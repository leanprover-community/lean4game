import { useAtomValue } from 'jotai'
import { useState } from 'react'
import { useTranslation } from 'react-i18next'
import { twMerge } from 'tailwind-merge'

import type { ApiGoal } from '../api'
import { mobileAtom } from '../state/preferences-atoms'
import { gameInfoAtom } from '../state/query-atoms'
import { HoverCode } from './HoverCode'
import { HypGroup } from './Hypothesis'

/**
 * The goals after the command, one tab per goal. With `insertable`, clicking the name of a
 * hypothesis inserts it in the active mask.
 */
export function GoalTabs({
  goals,
  current,
  insertable,
}: {
  goals: ApiGoal[]
  current: boolean
  insertable: boolean
}) {
  const { t } = useTranslation()
  const [selected, setSelected] = useState(0)
  const goal = goals.at(selected) ?? goals.at(0)
  if (!goal) return null
  return (
    <div>
      <div className="flex flex-wrap border-b border-(--border)">
        {goals.map((_, i) => (
          <button
            key={i}
            type="button"
            className={twMerge(
              'mx-0.5 cursor-pointer border-b-4 border-transparent px-4 py-0.5',
              goal === goals[i]
                ? twMerge('text-(--text-h)', current && 'border-primary')
                : 'text-(--text) hover:text-(--text-h)',
            )}
            onClick={() => setSelected(i)}
          >
            {i === 0
              ? t('typewriter.activeGoal')
              : t('typewriter.goalN', { n: i + 1 })}
          </button>
        ))}
      </div>
      <Goal goal={goal} insertable={insertable} />
    </div>
  )
}

/** The hypotheses, split into objects and assumptions, and the goal */
function Goal({ goal, insertable }: { goal: ApiGoal; insertable: boolean }) {
  const { t } = useTranslation()
  const mobile = useAtomValue(mobileAtom)
  const settings = useAtomValue(gameInfoAtom).data?.settings
  const unbundle = settings?.unbundleHyps
  // on mobile, the goal is below the hypotheses and always has the label
  const goalText = mobile || settings?.printGoalText
  // `A B : Prop` as `A : Prop` and `B : Prop`, if the game says so
  const hyps = unbundle
    ? goal.hyps.flatMap(hyp =>
        hyp.names.map(name => ({ ...hyp, names: [name] })),
      )
    : goal.hyps
  const objects = hyps.filter(hyp => !hyp.isAssumption)
  const assumptions = hyps.filter(hyp => hyp.isAssumption)
  return (
    <div
      className={twMerge(
        'flex py-1 font-mono text-(--text-h)',
        mobile && 'flex-col',
      )}
    >
      <div className="flex-col flex-1 justify-center">
        {objects.length > 0 && (
          <HypGroup
            title={t('typewriter.objects')}
            hyps={objects}
            insertable={insertable}
          />
        )}
        {assumptions.length > 0 && (
          <HypGroup
            title={t('typewriter.assumptions')}
            hyps={assumptions}
            insertable={insertable}
          />
        )}
      </div>
      {!mobile && (
        <svg className="mx-2 w-4 shrink-0 stroke-(--text) stroke-2">
          <line x1="0%" y1="0%" x2="0%" y2="100%" />
          <line x1="0%" y1="50%" x2="100%" y2="50%" />
        </svg>
      )}
      <div className="flex-col flex-1 justify-center">
        {goalText && (
          <div className="font-sans text-lg">{t('typewriter.goal')}:</div>
        )}
        <div className="whitespace-pre-wrap">
          <HoverCode code={goal.typeWithHover} fallback={goal.type} />
        </div>
      </div>
    </div>
  )
}
