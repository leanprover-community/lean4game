import { atom } from "jotai"
import { levelProgressAtom, progressAtom, defaultLevelProgress } from "./progress-atoms"
import { GameHint } from "../components/infoview/rpc_api"

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
    if (levelProgress == null) return
    set(levelProgressAtom, { ...levelProgress, help: [ ...val ] })
  }
)

/**
 * When deleting the proof, we want to keep to old messages around until
 * a new proof has been entered. e.g. to consult messages coming from dead ends
 */
export const deletedChatAtom = atom<GameHint[]>([])

/** Context to keep highlight selected proof step and corresponding chat messages. */
export const selectedStepAtom = atom<number>()
