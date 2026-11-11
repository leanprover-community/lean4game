import { atom } from 'jotai'

import { toastAtom } from '../../components/Toast'
import i18n from '../../i18n'
import type { Insertion } from '../mask-atoms'
import { insertionText } from './insertion'

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

/** Says what was inserted, shown by `Typewriter` */
export const typewriterToastAtom = toastAtom()

/** Inserts into the input field which was focused last, see `useInsertion` */
export const insertInTypewriterAtom = atom(
  null,
  (get, set, insertion: Insertion) => {
    const targets = get(insertTargetsAtom)
    const target = targets.reduce<InsertTarget | undefined>(
      (latest, t) => (!latest || t.focusedAt > latest.focusedAt ? t : latest),
      undefined,
    )
    if (!target) return
    target.insert(insertion)
    set(typewriterToastAtom, {
      text: i18n.t('masks.inserted', { text: insertionText(insertion) }),
    })
  },
)
