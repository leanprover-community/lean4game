import { atom } from 'jotai'

import type { Insertion } from '../mask-atoms'

/** An input field of the typewriter which takes insertions, see `useInsertion` */
export interface InsertTarget {
  insert: (insertion: Insertion) => void
  /** when the field was focused last, by `nextFocusTime`, 0 if never */
  focusedAt: number
}

let focusTime = 0

/** An increasing number to order the focusing of the input fields */
export function nextFocusTime() {
  return ++focusTime
}

/**
 * The input fields of the typewriter which are shown: the input line at the bottom, and
 * an earlier step while it is edited in place
 */
export const insertTargetsAtom = atom<InsertTarget[]>([])

/** Inserts into the input field which was focused last, see `useInsertion` */
export const insertInTypewriterAtom = atom(
  null,
  (get, _set, insertion: Insertion) => {
    const targets = get(insertTargetsAtom)
    const target = targets.reduce<InsertTarget | undefined>(
      (latest, t) => (!latest || t.focusedAt > latest.focusedAt ? t : latest),
      undefined,
    )
    target?.insert(insertion)
  },
)
