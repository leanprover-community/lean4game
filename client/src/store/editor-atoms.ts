import { editor, Selection as selector, } from 'monaco-editor'
import { atom } from "jotai";
import { atomEffect } from 'jotai-effect';
import { LeanMonaco, LeanMonacoOptions, LeanMonacoEditor, RpcSessionAtPos} from 'lean4monaco'
import { gameIdAtom, levelIdAtom, worldIdAtom } from "./location-atoms";
import { levelProgressAtom, progressAtom } from "./progress-atoms";
import { Selection } from "./progress-types";
import { levelInfoAtom } from "./query-atoms";
import { ProofState } from "../../../infoview/rpc_api";
import { Diagnostic, DiagnosticSeverity } from 'vscode-languageserver-types'
import { preferencesAtom } from './preferences-atoms';
import { deletedChatAtom } from './chat-atoms';
import { DocumentPosition } from '../components/infoview/types';

/** The unique leanMonaco instance for the entire application */
export const leanMonacoAtom = atom<LeanMonaco | null>(null)
export const leanMonacoEditorAtom = atom<editor.IStandaloneCodeEditor | null>(null)
export const oneLineEditorAtom = atom<editor.IStandaloneCodeEditor | null>(null)
/** The proof consists of multiple steps that are processed one after the other.
 * In particular multi-line terms like `match`-statements will not be supported.
 *
 * Note that the first step will always have "" as command
 */
export const proofAtom = atom<ProofState>()
export const rpcSessionAtom = atom<RpcSessionAtPos | null>(null)
export const isProcessingAtom = atom<Boolean>(false)
export const typewriterContentAtom = atom<string>("")

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

export const leanMonacoEditorModelAtom = atom(
  (get) => {
    const editor = get(leanMonacoEditorAtom)
    return editor?.getModel()
  }
)

export const leanMonacoEditorUriAtom = atom(
  (get) => {
    const model = get(leanMonacoEditorModelAtom)
    return model?.uri.toString() ?? ''
  }
)

export const hasLeanMonacoEditorAtom = atom(
  (get) => {
    const editor = get(leanMonacoEditorAtom)
    const model = get(leanMonacoEditorModelAtom)
    return Boolean(editor && model)
  })

export const codeAtom = atom(
  get => {
    const levelProgress = get(levelProgressAtom)
    return levelProgress?.code
  },
  (get, set, val: string) => {
    const levelProgress = get(levelProgressAtom)
    if (levelProgress == null) return
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
    if (levelProgress == null) return
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

export const restoreErrorCommandEffect = atomEffect(
  (get, set) => {
    const errorCommand = get(lastProofStepErrorCommandAtom)

    if (errorCommand) {
      set(typewriterContentAtom, errorCommand)
    }
  }
)

export const lastProofStepHasErrorsAtom = atom(
  (get) => {
    const proof = get(proofAtom)
    if (!proof?.steps.length) {
      return false
    }

    let diags = [...proof.steps[proof.steps.length - 1].diags, ...proof.diagnostics]

    return diags.some(
      (d) => (d.severity == DiagnosticSeverity.Error)
    )
  }
)

export const lastProofStepErrorCommandAtom = atom(
  (get) => {
    const proof = get(proofAtom)
    const hasErrors = get(lastProofStepHasErrorsAtom)

    if (!hasErrors || !proof?.steps) {
      return null
    }

    return proof.steps[proof.steps.length - 1].command
  }
)

/** TODO: Workaround to capture a crash of the gameserver. */
export const interimDiagsAtom = atom<Array<Diagnostic>>([])

/** TODO: Workaround to capture a crash of the gameserver. */
export const crashedAtom = atom<boolean>(false)

export const syncTypewriterToEditorEffect = atomEffect(
  (get, set) => {
    const oneLineEditor = get(oneLineEditorAtom)
    const typewriter = get(typewriterContentAtom)
    const { isSuggestionsMobileMode } = get(preferencesAtom)

    if (!oneLineEditor) {
      console.log("oneLineEditor is False")
      return
    }

    if (oneLineEditor.getValue() !== typewriter) {
      console.log(`Set value in oneLineEditor to ${typewriter}`)
      oneLineEditor.setValue(typewriter)
      oneLineEditor.setPosition({
        column: typewriter.length + 1,
        lineNumber: 1
      })
    }

    if (!isSuggestionsMobileMode) {
      oneLineEditor.focus()
    }
  }
)


export const syncEditorPositionEffect = atomEffect(
  (get, set) => {
    const oneLineEditor = get(oneLineEditorAtom)
    const editor = get(leanMonacoEditorAtom)
    const hasEditor = get(hasLeanMonacoEditorAtom)
    const { isSuggestionsMobileMode } = get(preferencesAtom)

    if (!oneLineEditor || !hasEditor || !editor) return

    oneLineEditor.setPosition({
      column: editor.getValue().length + 1,
      lineNumber: 1
    })

    if (!isSuggestionsMobileMode) {
      oneLineEditor.focus()
    }
  }
)

export const runCommandAtom = atom(
  null,
  (get, set) => {
    console.log("start running command")
    const processing = get(isProcessingAtom)
    const editor = get(oneLineEditorAtom)

    if (!editor){
      console.log("oneLineEditor not initialized")
      return
    }

    const hasEditor = get(hasLeanMonacoEditorAtom)
    const typewriter = get(typewriterContentAtom)

    if (processing || !hasEditor) {
      console.log("Editor not available or a process is currently running.")
      console.log(`Currently running a process: ${processing}`)
      console.log(`Does Editor exist: ${hasEditor}`)
      return
    }

    // TODO: Desired logic is to only reset this after a new *error-free* command has been entered
    set(deletedChatAtom, [])

    const pos = editor.getPosition()

    if (typewriter) {
      set(isProcessingAtom, true)

      editor.executeEdits("typewriter", [{
        range: selector.fromPositions(
          pos!,
          editor.getModel()?.getFullModelRange().getEndPosition()
        ),
        text: typewriter.trim() + "\n",
        forceMoveMarkers: false
      }])
      set(typewriterContentAtom, '')
      // Load proof after executing edits
      set(loadGoalsAtom)
    }

    editor.setPosition(pos!)
  }
)

export const loadGoalsAtom = atom(
  null,
  (get, set) => {
    const rpcSess = get(rpcSessionAtom)

    if (!rpcSess) {
      console.error("RpcSession is not available");
      return;
    }

    const uri = get(leanMonacoEditorUriAtom)
    const worldId = get(worldIdAtom)
    const levelId = get(levelIdAtom)

    console.info('sending rpc request to load the proof state')
    rpcSess.call('Game.getProofState',
        {
            ...DocumentPosition.toTdpp({line: 0, character: 0, uri: uri}),
            worldId, levelId
        }
    ).then(
      (proof: ProofState) => {
        if (typeof proof !== 'undefined') {
          console.info(`received a proof state!`)
          console.log(proof)
          set(proofAtom, proof)
          set(crashedAtom, false)
        } else {
          console.warn('received undefined proof state!')
          // Avoid transient crash state while the server warms up.
        }
      }
    ).catch((error: string) => {
      if (error === 'No connection to Lean') {
        console.warn(error)
        return
      }
      set(crashedAtom, true)
      console.warn(error)
    })
  }
)
