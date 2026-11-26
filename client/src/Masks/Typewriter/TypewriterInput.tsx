import { useAtom, useAtomValue, useSetAtom } from 'jotai'
import { useEffect, useRef } from 'react'
import { useTranslation } from 'react-i18next'

import { useFocusOnLevelOpen } from '../../hooks/useFocusOnLevelOpen'
import { proofCheckAtom } from '../../state/proof-atoms'
import { CommandInput, focusAtEnd } from './CommandInput'
import {
  submitTacticAtom,
  typewriterFocusAtom,
  typewriterInputAtom,
  typewriterInputHiddenAtom,
} from './typewriter-atoms'
import { useInsertion } from './useInsertion'

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
  const hidden = useAtomValue(typewriterInputHiddenAtom)
  // while hidden, there is no goal to insert at, see `insertInTypewriterAtom`
  const insertion = useInsertion(textareaRef, input, setInput, !hidden)

  // focus with the cursor at the end, also when it shows up again, e.g. after a retry
  useEffect(() => {
    if (focusRequest > 0 && !hidden) focusAtEnd(textareaRef.current)
  }, [focusRequest, hidden])

  // focus input when page loaded
  useFocusOnLevelOpen(textareaRef, !disabled && !hidden)

  if (hidden) return null

  return (
    <CommandInput
      ref={textareaRef}
      value={input}
      {...insertion}
      // the command stays until its result arrives, see `proofResultEffect`. An
      // unchanged proof is not checked again, the command just stays.
      onSubmit={submitTactic}
      disabled={disabled}
      pending={isFetching}
      placeholder={t('typewriter.inputPlaceholder')}
      className="shrink-0"
    />
  )
}
