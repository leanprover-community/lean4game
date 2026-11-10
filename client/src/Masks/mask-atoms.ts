import { atomWithStorage } from 'jotai/utils'

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
