import { useAtom, useAtomValue, useSetAtom } from 'jotai'
import { useEffect, useRef } from 'react'
import { useTranslation } from 'react-i18next'

import {
  hasError,
  proofCheckAtom,
  submitTacticAtom,
  typewriterFocusAtom,
  typewriterInputAtom,
} from '../../state/proof-atoms'
import { CommandInput, focusAtEnd } from './CommandInput'

/**
 * The input line at the bottom of the typewriter. While the proof is checked, it is
 * disabled and keeps the command, which stays there if it failed.
 */
export function TypewriterInput() {
  const { t } = useTranslation()
  const [input, setInput] = useAtom(typewriterInputAtom)
  const submitTactic = useSetAtom(submitTacticAtom)
  const focusRequest = useAtomValue(typewriterFocusAtom)
  const { data, error, isFetching } = useAtomValue(proofCheckAtom)
  const textareaRef = useRef<HTMLTextAreaElement>(null)
  // a new command must be based on the result of the previous one
  const disabled = isFetching || (!data && !error)

  // nothing to do once there are no goals left
  const last = data?.steps.at(-1)
  const hidden =
    last !== undefined && !hasError(last) && last.goals.length === 0

  // focus with the cursor at the end, also when it shows up again, e.g. after a retry
  useEffect(() => {
    if (focusRequest > 0 && !hidden) focusAtEnd(textareaRef.current)
  }, [focusRequest, hidden])

  if (hidden) return null

  return (
    <CommandInput
      ref={textareaRef}
      value={input}
      onChange={setInput}
      // the command stays until its result arrives, see `proofResultEffect`. An
      // unchanged proof is not checked again, the command just stays.
      onSubmit={submitTactic}
      disabled={disabled}
      placeholder={t('typewriter.inputPlaceholder')}
      className="shrink-0"
    />
  )
}
