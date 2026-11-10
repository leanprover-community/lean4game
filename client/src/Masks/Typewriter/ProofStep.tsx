import { faDeleteLeft, faXmark } from '@fortawesome/free-solid-svg-icons'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { useAtom, useAtomValue, useSetAtom } from 'jotai'
import { useEffect, useRef, useState } from 'react'
import { useTranslation } from 'react-i18next'
import { twMerge } from 'tailwind-merge'

import type { ApiDiagnostic, ApiGoal, ApiProofStep } from '../../api'
import { InlineHints } from '../../Chat/Chat'
import { useStepSelection } from '../../hooks/useStepSelection'
import { mobileAtom } from '../../state/preferences-atoms'
import { proofCheckAtom } from '../../state/proof-atoms'
import { CommandInput, focusAtEnd } from './CommandInput'
import { HoverCode } from './HoverCode'
import { HypGroup } from './Hypothesis'
import {
  editingStepAtom,
  replaceStepAtom,
  retryFromStepAtom,
} from './typewriter-atoms'
import { useInsertion } from './useInsertion'

/**
 * A step of the proof: the entered command, the messages Lean produced and the goals
 * afterwards. `current` is the step the next command continues from, `failed` is a last
 * step with errors, which is replaced by the next command.
 */
export function ProofStep({
  step,
  index,
  current,
  failed,
}: {
  step: ApiProofStep
  index: number
  current: boolean
  failed: boolean
}) {
  const mobile = useAtomValue(mobileAtom)
  const selection = useStepSelection(index)
  return (
    <div
      {...selection.props}
      className={twMerge('my-2 rounded-lg p-2', selection.className)}
    >
      {index > 0 && (
        <Command step={step} index={index} current={current} failed={failed} />
      )}
      <Diagnostics diagnostics={step.diagnostics} />
      {mobile && !failed && <InlineHints step={index} />}
      {!failed && <GoalTabs goals={step.goals} current={current} />}
    </div>
  )
}

/**
 * The entered command, with a button to retry the proof from here. For the last command,
 * this puts it into the input line at the bottom, earlier commands are edited in place.
 */
function Command({
  step,
  index,
  current,
  failed,
}: {
  step: ApiProofStep
  index: number
  current: boolean
  failed: boolean
}) {
  const { t } = useTranslation()
  const retryFromStep = useSetAtom(retryFromStepAtom)
  const [editingStep, setEditingStep] = useAtom(editingStepAtom)
  if (failed) {
    return (
      <div className="mb-4 flex-col rounded-sm bg-(--section-bg) p-2">
        <i>{t('typewriter.failedCommand')}:</i>
        <span className="font-mono whitespace-pre-wrap">{step.tactic}</span>
      </div>
    )
  }
  if (editingStep === index) return <EditCommand step={step} index={index} />
  return (
    <div className="mb-4 flex gap-2 rounded-sm bg-gray-300 p-2 dark:bg-gray-700">
      <div
        className={twMerge(
          'flex-1 bg-(--bg) px-2.5 pt-1.5 font-mono text-sm whitespace-pre-wrap',
          'text-(--text-h)',
        )}
      >
        {step.tactic}
      </div>
      <button
        type="button"
        className={twMerge(
          'h-7.5 min-w-24 shrink-0 cursor-pointer self-start rounded-sm bg-(--bg)',
          'px-2 whitespace-nowrap text-gray-500 hover:text-primary',
        )}
        title={t('typewriter.retryTitle')}
        onClick={() => (current ? retryFromStep(index) : setEditingStep(index))}
      >
        <FontAwesomeIcon icon={faDeleteLeft} />
        &nbsp;{t('typewriter.retry')}
      </button>
    </div>
  )
}

/**
 * An earlier command, edited in place. Only executing it deletes the rest of the proof
 * and checks it with the new command; while checking, it is disabled.
 */
function EditCommand({ step, index }: { step: ApiProofStep; index: number }) {
  const { t } = useTranslation()
  const [text, setText] = useState(step.tactic)
  const setEditingStep = useSetAtom(editingStepAtom)
  const replaceStep = useSetAtom(replaceStepAtom)
  const { isFetching } = useAtomValue(proofCheckAtom)
  const textareaRef = useRef<HTMLTextAreaElement>(null)
  // takes the insertions while it was focused last, which it is when it opens
  const insertion = useInsertion(textareaRef, text, setText)

  useEffect(() => focusAtEnd(textareaRef.current), [])

  return (
    <CommandInput
      ref={textareaRef}
      value={text}
      {...insertion}
      // closed once the result of the new proof arrives, see `proofResultEffect`
      onSubmit={value => {
        if (!replaceStep(index, value)) setEditingStep(null)
      }}
      onCancel={() => setEditingStep(null)}
      disabled={isFetching}
      className="mb-4 rounded-sm"
    >
      <button
        type="button"
        className={twMerge(
          'size-7.5 shrink-0 cursor-pointer rounded-sm bg-(--bg)',
          'text-gray-500 hover:text-primary',
        )}
        title={t('typewriter.cancelEdit')}
        aria-label={t('typewriter.cancelEdit')}
        onClick={() => setEditingStep(null)}
      >
        <FontAwesomeIcon icon={faXmark} />
      </button>
    </CommandInput>
  )
}

const severityClass: Record<number, string> = {
  1: 'bg-red-100 text-red-700 dark:bg-red-950 dark:text-red-300',
  2: 'bg-amber-100 text-amber-800 dark:bg-amber-950 dark:text-amber-200',
  3: 'bg-sky-100 text-(--text-h) dark:bg-sky-950',
  4: 'bg-sky-100 text-(--text-h) dark:bg-sky-950',
}

/** The messages (error/warning/information) produced by the command */
function Diagnostics({ diagnostics }: { diagnostics: ApiDiagnostic[] }) {
  const shown = diagnostics.filter(d => d.message.trim().length > 0)
  return shown.map((d, i) => (
    <div
      key={i}
      className={twMerge(
        'my-2.5 overflow-x-auto rounded-sm px-2.5 py-1.5',
        severityClass[d.severity],
      )}
    >
      <pre className="m-0 font-mono text-sm whitespace-pre-wrap">
        {d.message}
      </pre>
    </div>
  ))
}

/** The goals after the command, one tab per goal */
function GoalTabs({ goals, current }: { goals: ApiGoal[]; current: boolean }) {
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
      <Goal goal={goal} />
    </div>
  )
}

/** The hypotheses, split into objects and assumptions, and the goal */
function Goal({ goal }: { goal: ApiGoal }) {
  const { t } = useTranslation()
  const mobile = useAtomValue(mobileAtom)
  const objects = goal.hyps.filter(hyp => !hyp.isAssumption)
  const assumptions = goal.hyps.filter(hyp => hyp.isAssumption)
  return (
    <div
      className={twMerge(
        'flex py-1 font-mono text-(--text-h)',
        mobile && 'flex-col',
      )}
    >
      <div className="flex-col flex-1 justify-center">
        {objects.length > 0 && (
          <HypGroup title={t('typewriter.objects')} hyps={objects} />
        )}
        {assumptions.length > 0 && (
          <HypGroup title={t('typewriter.assumptions')} hyps={assumptions} />
        )}
      </div>
      {!mobile && (
        <svg className="mx-2 w-4 shrink-0 stroke-(--text) stroke-2">
          <line x1="0%" y1="0%" x2="0%" y2="100%" />
          <line x1="0%" y1="50%" x2="100%" y2="50%" />
        </svg>
      )}
      <div className="flex-col flex-1 justify-center">
        {mobile && (
          <div className="font-sans text-lg">{t('typewriter.goal')}:</div>
        )}
        <div className="whitespace-pre-wrap">
          <HoverCode code={goal.typeWithHover} fallback={goal.type} />
        </div>
      </div>
    </div>
  )
}
