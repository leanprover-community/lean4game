import { atom } from 'jotai'
import { atomEffect } from 'jotai-effect'

import { levelIdAtom, worldIdAtom } from '../state/location-atoms'
import { levelProgressAtom, progressAtom } from '../state/progress-atoms'

/** User read the game introduction, see `leftPanelOpenAtom`. Only relevant on mobile */
export const readGameIntroAtom = atom(
  get => {
    const progress = get(progressAtom)
    if (!progress) return false
    return progress.readIntro
  },
  (get, set, val: boolean) => {
    const progress = get(progressAtom)
    if (!progress) return
    set(progressAtom, { ...progress, readIntro: val })
  },
)

/**
 * The number of revealed hidden hints by proof step. They are stored as a list of
 * steps, one entry per revealed hint. Setting a step reveals its next hidden hint.
 */
export const helpAtom = atom(
  get => {
    const counts = new Map<number, number>()
    for (const step of get(levelProgressAtom)?.help ?? []) {
      counts.set(step, (counts.get(step) ?? 0) + 1)
    }
    return counts
  },
  (get, set, step: number) => {
    const levelProgress = get(levelProgressAtom)
    if (levelProgress == null) return
    set(levelProgressAtom, {
      ...levelProgress,
      help: [...levelProgress.help, step],
    })
  },
)

/** The selected proof step, highlighted with its chat messages, see `useStepSelection` */
export const selectedStepAtom = atom<number>()

/** Clears the selection when going to another level */
export const resetSelectedStepEffect = atomEffect((get, set) => {
  get(worldIdAtom)
  get(levelIdAtom)
  set(selectedStepAtom, undefined)
})
