import { atom } from 'jotai'

import { toastAtom } from '../../components/Toast'
import i18n from '../../i18n'
import type { Insertion } from '../mask-atoms'
import { insertionText } from '../Typewriter/insertion'

/** Says what an insertion copied, shown by the raw mask */
export const rawToastAtom = toastAtom()

/**
 * The raw mask has no input line to insert into, so it copies the text to the clipboard:
 * a tactic's template without its slots, e.g. `rw []`, or a name
 */
export const insertInRawAtom = atom(
  null,
  async (_get, set, insertion: Insertion) => {
    const text = insertionText(insertion)
    try {
      await navigator.clipboard.writeText(text)
      set(rawToastAtom, { text: i18n.t('masks.copied', { text }) })
    } catch {
      // e.g. not allowed by the browser
      set(rawToastAtom, {
        text: i18n.t('masks.copyFailed', { text }),
        error: true,
      })
    }
  },
)
