import { atom } from "jotai";
import { LeanMonaco, LeanMonacoOptions } from 'lean4monaco'
import { gameIdAtom } from "./location-atoms";

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
