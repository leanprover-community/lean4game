import { faDeleteLeft, faXmark } from '@fortawesome/free-solid-svg-icons'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { useAtom, useAtomValue, useSetAtom } from 'jotai'
import { useEffect, useRef, useState } from 'react'
import { useTranslation } from 'react-i18next'
import { twMerge } from 'tailwind-merge'

import type { ApiDiagnostic, ApiProofStep } from '../../api'
import { InlineHints } from '../../Chat/Chat'
import { GoalTabs } from '../../GoalView/GoalTabs'
import { useStepSelection } from '../../hooks/useStepSelection'
import { mobileAtom } from '../../state/preferences-atoms'
import { proofCheckAtom } from '../../state/proof-atoms'
import { CommandInput, focusAtEnd } from './CommandInput'
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
      {!failed && <GoalTabs goals={step.goals} current={current} insertable />}
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
  const mobile = useAtomValue(mobileAtom)
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
          'h-7.5 shrink-0 cursor-pointer self-start rounded-sm bg-(--bg)',
          'whitespace-nowrap text-gray-500 hover:text-primary',
          mobile ? 'w-7.5' : 'min-w-24 px-2',
        )}
        title={t('typewriter.retryTitle')}
        aria-label={t('typewriter.retry')}
        onClick={() => (current ? retryFromStep(index) : setEditingStep(index))}
      >
        <FontAwesomeIcon icon={faDeleteLeft} />
        {!mobile && <>&nbsp;{t('typewriter.retry')}</>}
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
      pending={isFetching}
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
