import { atom } from 'jotai'

import type { Insertion } from '../mask-atoms'
import { parseTemplate } from '../Typewriter/insertion'

/** The last text copied by an insertion, and whether that worked, see `CopyToast` */
export interface RawCopy {
  text: string
  copied: boolean
  /** to tell copies of the same text apart */
  id: number
}

export const rawCopyAtom = atom<RawCopy | null>(null)

/**
 * The raw mask has no input line to insert into, so it copies the text to the clipboard:
 * a tactic's template without its slots, e.g. `rw []`, or a name
 */
export const insertInRawAtom = atom(
  null,
  async (get, set, insertion: Insertion) => {
    const text =
      insertion.kind === 'tactic'
        ? parseTemplate(insertion.template).text.trim()
        : insertion.name
    let copied = true
    try {
      await navigator.clipboard.writeText(text)
    } catch {
      // e.g. not allowed by the browser
      copied = false
    }
    set(rawCopyAtom, { text, copied, id: (get(rawCopyAtom)?.id ?? 0) + 1 })
  },
)
