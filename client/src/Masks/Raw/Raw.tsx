import { faSpinner } from '@fortawesome/free-solid-svg-icons'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { useAtom, useAtomValue } from 'jotai'
import { useRef, useState } from 'react'
import { useTranslation } from 'react-i18next'
import { twMerge } from 'tailwind-merge'

import { Toast } from '../../components/Toast'
import { WorldImage } from '../../components/WorldImage'
import { proofOfCode } from '../../state/progress-schema'
import {
  leanInstanceAtom,
  proofAtom,
  proofCheckAtom,
} from '../../state/proof-atoms'
import { levelInfoAtom } from '../../state/query-atoms'
import { useLeanPhaseText } from '../LeanProgress'
import { AbbreviationBar } from '../Typewriter/CommandInput'
import { useAbbreviations } from '../Typewriter/useAbbreviations'
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

  return (
    <div className="relative h-full">
      <div
        className={twMerge(
          'flex-col h-full overflow-y-auto p-2 text-left font-mono text-sm',
          'leading-normal text-(--text-h)',
        )}
      >
        <pre className="m-0 shrink-0 px-2 pb-1 wrap-break-word whitespace-pre-wrap [font:inherit]">
          {levelInfo?.descrFormat ?? ''}
        </pre>
        <div className="relative flex-col min-h-0 flex-1">
          <WorldImage className="object-bottom opacity-50" />
          <div className="relative flex max-h-max min-h-0 flex-[1_1_0] bg-(--bg)">
            <span aria-hidden className="whitespace-pre select-none">
              {'  '}
            </span>
            <textarea
              ref={textareaRef}
              className={twMerge(
                'block min-h-[calc(3lh+1rem)] min-w-0 flex-1 resize-none rounded-sm',
                'border-0 bg-(--code-bg) p-2 [font:inherit] text-inherit',
                'field-sizing-content focus:ring-1 focus:ring-primary focus:outline-none',
              )}
              aria-label={t('masks.proof')}
              value={text}
              onChange={() => abbreviations.input()}
              onSelect={() => abbreviations.select()}
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
      </div>
      <Toast messageAtom={rawToastAtom} />
    </div>
  )
}
