import { faSpinner } from '@fortawesome/free-solid-svg-icons'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { useAtom, useAtomValue } from 'jotai'
import { useState } from 'react'
import { useTranslation } from 'react-i18next'
import { twMerge } from 'tailwind-merge'

import { WorldImage } from '../../components/WorldImage'
import { proofOfCode } from '../../state/progress-schema'
import {
  leanInstanceAtom,
  proofAtom,
  proofCheckAtom,
} from '../../state/proof-atoms'
import { levelInfoAtom } from '../../state/query-atoms'
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

  return (
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
            className={twMerge(
              'block min-h-[calc(3lh+1rem)] min-w-0 flex-1 resize-none rounded-sm',
              'border-0 bg-(--code-bg) p-2 [font:inherit] text-inherit',
              'field-sizing-content focus:ring-1 focus:ring-primary focus:outline-none',
            )}
            aria-label={t('masks.proof')}
            value={text}
            onChange={event => onChange(event.target.value)}
            spellCheck={false}
            autoCapitalize="off"
            autoCorrect="off"
          />
          {waiting && (
            <output className="pointer-events-none absolute right-2 bottom-1.5 opacity-50">
              <span className="sr-only">{t('masks.checking')}</span>
              <FontAwesomeIcon icon={faSpinner} spinPulse aria-hidden />
            </output>
          )}
        </div>
        <Transcript text={text} />
      </div>
    </div>
  )
}
