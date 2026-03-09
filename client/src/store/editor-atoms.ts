import { atom } from "jotai";
import { LeanMonaco, LeanMonacoOptions } from 'lean4monaco'
import { gameIdAtom } from "./location-atoms";
import { levelProgressAtom, progressAtom } from "./progress-atoms";
import { Selection } from "./progress-types";

/** Options for the LeanMonaco instance */
export const leanMonacoOptionsAtom = atom<LeanMonacoOptions>(get => {
  const gameId = get(gameIdAtom)
  return {
  websocket: {
    url: ((window.location.protocol === "https:") ? "wss://" : "ws://") + window.location.host + '/websocket/' + gameId
  },
  htmlElement: undefined, // The wrapper div for monaco
  vscode: {
    // The default options are defined in `LeanMonaco.start` and can be overwritten here.
    // See docstring of `LeanMonacoOptions`!
    // For example:
    "editor.wordWrap": true,
  }
}})

/** The unique leanMonaco instance for the entire application */
export const leanMonacoAtom = atom<LeanMonaco | null>(null)

/** Whether the current game is in typewriter mode */
export const typewriterModeAtom = atom(
  get => {
    const progress = get(progressAtom)
    if (!progress) return false
    return progress.typewriterMode
  },
  (get, set, val: boolean | null) => {
    const progress = get(progressAtom)
    if (!progress) return
    const valMod = (val === null) ? undefined : val
    set(progressAtom, { ...progress, typewriterMode: valMod })
  }
)

export const codeAtom = atom(
  get => {
    const levelProgress = get(levelProgressAtom)
    return levelProgress?.code
  },
  (get, set, val: string) => {
    const levelProgress = get(levelProgressAtom)
    if (!levelProgress) return
    set(levelProgressAtom, { ...levelProgress, code: val })
  }
)

export const selectionsAtom = atom(
  get => {
    const levelProgress = get(levelProgressAtom)
    return levelProgress?.selections ?? []
  },
  (get, set, val: Selection[]) => {
    const levelProgress = get(levelProgressAtom)
    if (!levelProgress) return
    set(levelProgressAtom, { ...levelProgress, selections: val })
  }
)
