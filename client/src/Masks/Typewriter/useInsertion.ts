import { useSetAtom } from 'jotai'
import { type RefObject, useEffect, useRef, useState } from 'react'

import type { Insertion } from '../mask-atoms'
import {
  editText,
  type InputState,
  insertName,
  insertTemplate,
} from './insertion'
import {
  type InsertTarget,
  insertTargetsAtom,
  nextFocusTime,
} from './typewriter-insert-atoms'

/** The state of `text` without slots, with the caret at the end */
function plainState(text: string): InputState {
  return { text, slots: [], selection: [text.length, text.length] }
}

/**
 * Makes an input field of the typewriter take insertions, see `insertion.ts`: it keeps
 * the slots of inserted templates and the last selection, also while the focus is
 * elsewhere. They belong to the text, so when it is changed from outside, e.g. cleared
 * after submitting, they are dropped. While the field is shown, it gets the insertions if
 * it was focused last, or if no other field was focused since.
 *
 * Returns the handlers to pass to `CommandInput`.
 */
export function useInsertion(
  ref: RefObject<HTMLTextAreaElement | null>,
  text: string,
  setText: (text: string) => void,
) {
  const setTargets = useSetAtom(insertTargetsAtom)
  const [stored, setStored] = useState(() => plainState(text))
  const state = stored.text === text ? stored : plainState(text)
  // incremented to focus the field with the selection of `state`, after an insertion
  const [focusRequest, setFocusRequest] = useState(0)

  const update = (next: InputState) => {
    setStored(next)
    if (next.text !== text) setText(next.text)
  }

  // the latest `insert`, called through the stable `target`
  const insertRef = useRef<(insertion: Insertion) => void>(undefined)
  insertRef.current = (insertion: Insertion) => {
    update(
      insertion.kind === 'tactic'
        ? insertTemplate(state, insertion.template)
        : insertName(state, insertion.name),
    )
    setFocusRequest(n => n + 1)
  }
  const [target] = useState<InsertTarget>(() => ({
    insert: insertion => insertRef.current?.(insertion),
    focusedAt: 0,
  }))

  // while shown, the field takes insertions if no other one was focused after it
  useEffect(() => {
    setTargets(targets => [...targets, target])
    return () => setTargets(targets => targets.filter(t => t !== target))
  }, [setTargets, target])

  const selection = state.selection
  useEffect(() => {
    const textarea = ref.current
    if (focusRequest === 0 || !textarea) return
    textarea.focus()
    textarea.setSelectionRange(...selection)
    // only when requested, not on every change of the selection
    // oxlint-disable-next-line react-hooks/exhaustive-deps
  }, [focusRequest])

  return {
    /** moves the slots along with the edit */
    onChange: (value: string) =>
      update(editText(state, value, ref.current?.selectionEnd)),
    onSelectionChange: (newSelection: [number, number]) =>
      setStored({ ...state, selection: newSelection }),
    /** takes the insertions from now on */
    onFocus: () => {
      target.focusedAt = nextFocusTime()
    },
  }
}
