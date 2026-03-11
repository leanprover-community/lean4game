import { atom } from "jotai";
import { LeanMonaco, LeanMonacoOptions } from 'lean4monaco'
import { gameIdAtom } from "./location-atoms";
import { levelProgressAtom, progressAtom } from "./progress-atoms";
import { Selection } from "./progress-types";
import { levelInfoAtom } from "./query-atoms";
import { ProofState } from "../components/infoview/rpc_api";
import { Diagnostic } from 'vscode-languageserver-types'

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

export const typewriterContentAtom = atom<string>("")

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

/** If a level has a template, the user is forced to use editor mode */
export const lockEditorModeAtom = atom(get => {
  const { data: levelInfo } = get(levelInfoAtom)
  return levelInfo?.template != null
})

/** Whether the current game is in typewriter mode */
export const typewriterModeAtom = atom(
  get => {
    // force editor mode
    const lockEditorMode = get(lockEditorModeAtom)
    if (lockEditorMode) return false

    // read setting from local storage
    const progress = get(progressAtom)
    return progress?.typewriterMode ?? true
  },
  (get, set, val: boolean | null) => {
    const progress = get(progressAtom)
    if (!progress) return
    const valMod = (val === null) ? undefined : val
    set(progressAtom, { ...progress, typewriterMode: valMod })
  }
)

/** The proof consists of multiple steps that are processed one after the other.
 * In particular multi-line terms like `match`-statements will not be supported.
 *
 * Note that the first step will always have "" as command
 */
export const proofAtom = atom<ProofState>()

/** TODO: Workaround to capture a crash of the gameserver. */
export const interimDiagsAtom = atom<Array<Diagnostic>>()

/** TODO: Workaround to capture a crash of the gameserver. */
export const crashedAtom = atom<boolean>()
