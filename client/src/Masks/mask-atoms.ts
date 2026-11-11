import { atom } from 'jotai'
import { atomWithStorage } from 'jotai/utils'

import { rightPanelOpenAtom } from '../state/layout-atoms'
import { mobileAtom } from '../state/preferences-atoms'
import { insertInRawAtom } from './Raw/raw-insert-atoms'
import { insertInTypewriterAtom } from './Typewriter/typewriter-insert-atoms'

/**
 * The interfaces to play a level with, shown in the center of the level page. An object
 * instead of an `enum`, which `erasableSyntaxOnly` does not allow; use it the same way,
 * e.g. `Mask.Typewriter`. The values are stored, and they are the i18next context of
 * the translations `masks.name_…`.
 */
export const Mask = {
  Typewriter: 'typewriter',
  Raw: 'raw',
} as const

export type Mask = (typeof Mask)[keyof typeof Mask]

/** All masks, in the order of the menu */
export const masks: Mask[] = Object.values(Mask)

/** The mask the player has selected, kept in local storage */
export const maskAtom = atomWithStorage<Mask>(
  'mask',
  Mask.Typewriter,
  undefined,
  {
    getOnInit: true,
  },
)

/**
 * What to insert into the active mask: a tactic by its template, see `TacticDoc` on the
 * Lean side, or the name of a theorem, definition or hypothesis
 */
export type Insertion =
  | { kind: 'tactic'; template: string }
  | { kind: 'name'; name: string }

/**
 * Asks the active mask to insert something, e.g. a tactic from the inventory or a
 * hypothesis. How is up to the mask: the typewriter inserts it into its input line, the
 * raw mask copies it to the clipboard.
 */
export const insertAtom = atom(null, (get, set, insertion: Insertion) => {
  // on mobile, the inventory covers the mask, so it gets out of the way
  if (get(mobileAtom)) set(rightPanelOpenAtom, false)
  switch (get(maskAtom)) {
    case Mask.Typewriter:
      set(insertInTypewriterAtom, insertion)
      break
    case Mask.Raw:
      void set(insertInRawAtom, insertion)
      break
  }
})
