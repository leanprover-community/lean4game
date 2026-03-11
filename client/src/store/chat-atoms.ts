import { atom } from "jotai"
import { levelProgressAtom, progressAtom } from "./progress-atoms"

/** User read the game introduction. Only relevant on mobile */
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
  }
)

export const helpAtom = atom(
  get => {
    const levelProgress = get(levelProgressAtom)
    return new Set(levelProgress?.help ?? [])
  },
  (get, set, val: Set<number>) => {
    const levelProgress = get(levelProgressAtom)
    if (!levelProgress) return
    set(levelProgressAtom, { ...levelProgress, help: [ ...val ] })
  }
)
