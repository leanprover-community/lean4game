import { faSpinner } from '@fortawesome/free-solid-svg-icons'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { useAtom, useAtomValue } from 'jotai'
import { useRef, useState } from 'react'
import { useTranslation } from 'react-i18next'
import { twMerge } from 'tailwind-merge'

import { Toast } from '../../components/Toast'
import { WorldImage } from '../../components/WorldImage'
import { GoalTabs } from '../../GoalView/GoalTabs'
import { HoverProvider } from '../../GoalView/HoverCode'
import { useAbbreviations } from '../../hooks/useAbbreviations'
import { proofOfCode } from '../../state/progress-schema'
import {
  hasError,
  leanInstanceAtom,
  proofAtom,
  proofCheckAtom,
} from '../../state/proof-atoms'
import { levelInfoAtom } from '../../state/query-atoms'
import { useLeanPhaseText } from '../LeanProgress'
import { AbbreviationBar } from '../Typewriter/CommandInput'
import { stepAtLine } from './proof-lines'
import { rawToastAtom } from './raw-insert-atoms'
import { Transcript } from './Transcript'

/** Whether two proofs have the same steps */
function sameProof(a: string[], b: string[]) {
  return a.length === b.length && a.every((step, i) => step === b[i])
}

/**
 * A minimalistic mask showing the source code. Mostly intended for debugging
 * to copy code to and from the game.
 */
export function Raw() {
  const { t } = useTranslation()
  const levelInfo = useAtomValue(levelInfoAtom).data
  const [proof, setProof] = useAtom(proofAtom)
  const instance = useAtomValue(leanInstanceAtom)
  const check = useAtomValue(proofCheckAtom)
  // the Lean instance is starting, or the proof is checked
  const waiting = instance.isPending || check.isFetching
  // before the first result, e.g. while the imports of the game are loaded
  const phaseText = useLeanPhaseText()
  const waitingText = check.data === undefined ? phaseText : t('masks.checking')
  // the text as typed, which keeps e.g. empty lines that are not part of the proof
  const [text, setText] = useState(() => proof.join('\n'))

  // take over a proof changed elsewhere, e.g. when going to another level
  const [shownProof, setShownProof] = useState(proof)
  if (proof !== shownProof) {
    setShownProof(proof)
    if (!sameProof(proofOfCode(text), proof)) setText(proof.join('\n'))
  }

  const onChange = (value: string) => {
    setText(value)
    const newProof = proofOfCode(value)
    if (!sameProof(newProof, proof)) setProof(newProof)
  }
  const textareaRef = useRef<HTMLTextAreaElement>(null)
  const abbreviations = useAbbreviations(textareaRef, text, onChange)
  // the 0-based line of the text field whose goals are shown below: the cursor's line, or
  // the line above while the cursor is at the beginning of a line, i.e. before its tactic.
  // `-1` before the first line, for the initial goals.
  const [cursorLine, setCursorLine] = useState(-1)
  const updateCursorLine = () => {
    const textarea = textareaRef.current
    if (!textarea) return
    const lines = textarea.value.slice(0, textarea.selectionStart).split('\n')
    const atLineStart = lines.at(-1)?.trim() === ''
    setCursorLine(lines.length - (atLineStart ? 2 : 1))
  }

  return (
    <div className="relative h-full">
      {/* behind the whole mask, so that it doesn't move when the parts change their size */}
      <WorldImage className="object-center opacity-50" />
      {/* the statement and the goals stay, the proof and the messages in between scroll */}
      <div
        className={twMerge(
          'relative flex-col h-full p-2 text-left font-mono text-sm',
          'leading-normal text-(--text-h)',
        )}
      >
        <pre className="m-0 shrink-0 px-2 pb-1 wrap-break-word whitespace-pre-wrap [font:inherit]">
          {levelInfo?.descrFormat ?? ''}
        </pre>
        <div className="relative flex-col min-h-0 flex-1">
          {/* at most half of the space, then the text field scrolls */}
          <div className="relative flex-col max-h-1/2 min-h-0 bg-(--bg) pl-[2ch]">
            <textarea
              ref={textareaRef}
              className={twMerge(
                'block min-h-[calc(3lh+1rem)] w-full resize-none rounded-sm',
                'border-0 bg-(--code-bg) p-2 [font:inherit] text-inherit',
                'field-sizing-content focus:ring-1 focus:ring-primary focus:outline-none',
              )}
              aria-label={t('masks.proof')}
              value={text}
              onChange={() => {
                abbreviations.input()
                updateCursorLine()
              }}
              onSelect={() => {
                abbreviations.select()
                updateCursorLine()
              }}
              onCompositionStart={() => abbreviations.compositionStart()}
              onCompositionEnd={() => abbreviations.compositionEnd()}
              onKeyDown={ev => {
                // otherwise Tab moves the focus as usual
                if (ev.key === 'Tab' && abbreviations.tracking) {
                  ev.preventDefault()
                  void abbreviations.replaceAll()
                }
              }}
              spellCheck={false}
              autoCapitalize="off"
              autoCorrect="off"
            />
            {waiting && (
              <output
                className="pointer-events-none absolute right-2 bottom-1.5 opacity-50"
                title={waitingText}
              >
                <span className="sr-only">{waitingText}</span>
                <FontAwesomeIcon icon={faSpinner} spinPulse aria-hidden />
              </output>
            )}
            <AbbreviationBar
              abbreviations={abbreviations}
              below
              className="left-[2ch] mt-px"
            />
          </div>
          <Transcript text={text} />
        </div>
        <CursorGoals text={text} cursorLine={cursorLine} />
      </div>
      <Toast messageAtom={rawToastAtom} />
    </div>
  )
}

/**
 * The goals after the step at the cursor, like in the typewriter, with a tab per goal, or
 * before it if it has an error. At the bottom of the mask, at most a third of its height.
 */
function CursorGoals({
  text,
  cursorLine,
}: {
  text: string
  cursorLine: number
}) {
  const { t } = useTranslation()
  const check = useAtomValue(proofCheckAtom)
  const result = check.data
  if (!result) return null
  let index = stepAtLine(result.steps, text, cursorLine)
  // a step with an error has no goals: the goals it failed on
  while (index > 0 && hasError(result.steps.at(index))) index--
  const step = result.steps.at(index)
  if (!step) return null
  return (
    <section
      aria-label={t('typewriter.goal')}
      className={twMerge(
        'mt-2 max-h-1/3 shrink-0 overflow-y-auto rounded-sm bg-(--section-bg) px-2',
        'font-sans text-base',
        check.isPlaceholderData && 'opacity-60',
      )}
    >
      <HoverProvider hovers={result.hovers} hoverDocs={result.hoverDocs}>
        {step.goals.length > 0 ? (
          // back to the first goal at another step
          <GoalTabs key={index} goals={step.goals} current insertable={false} />
        ) : (
          <p className="m-0 py-2 text-(--text)">
            {t('typewriter.noGoalsLeft')}
          </p>
        )}
      </HoverProvider>
    </section>
  )
}
