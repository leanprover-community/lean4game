import { editor, Selection as selector, } from 'monaco-editor'
import { atom } from "jotai";
import { atomEffect } from 'jotai-effect';
import { LeanMonaco, LeanMonacoOptions, DocumentPosition, RpcSessionAtPos, LeanClient} from 'lean4monaco'
import { gameIdAtom, levelIdAtom, worldIdAtom } from "./location-atoms";
import { levelProgressAtom, progressAtom } from "./progress-atoms";
import { Selection } from "./progress-types";
import { levelInfoAtom } from "./query-atoms";
import { Diagnostic, DiagnosticSeverity, DocumentUri } from 'vscode-languageserver-types'
import { preferencesAtom } from './preferences-atoms';
import { deletedChatAtom } from './chat-atoms';
import { ProofState } from '../api/rpc_api';

import { defaultInfoviewConfig, InfoviewConfig, LeanFileProgressProcessingInfo } from '@leanprover/infoview-api';
import { atomWithQuery } from 'jotai-tanstack-query';
import { Rpc } from 'lean4monaco/dist/vscode-lean4/vscode-lean4/src/rpc';

/** The code of the current level as stored in local storage.
 *
 * The setter must not be used directly, expect inside the
 * listener which listens to changes of the editor's content.
 * This is because the editor won't update leading to inconsistent state.
 *
 * Instead, use `codeAtom` to set the editor's content and the code
 * in storage.
*/
export const codeStorageAtom = atom(
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

/** The unique leanMonaco instance for the entire application */
export const leanMonacoAtom = atom<LeanMonaco | null>(null)

/** The active client. lean4game only uses one client simultaneously */
export const clientAtom = atom<LeanClient>()
//   get => {
//   const clients = get(leanMonacoAtom)?.clientProvider?.getClients() ?? []
//   return clients?.[0]
// })

/** The current (multiline) editor */
export const editorAtom = atom<editor.IStandaloneCodeEditor | null>(null)

/** The model of the current editor */
export const modelAtom = atom(get => get(editorAtom)?.getModel() ?? undefined)

/**
 * The code of the current level as stored in local storage.
 *
 * Can be used to manually update the editor's content which
 * in turn keeps the code in local storage up to date.
*/
export const codeAtom = atom(
  get => get(codeStorageAtom),
  (get, set, val: string) => {
    const model = get(modelAtom)
    model?.setValue(val)
  }
)

/** The URI of the currently opened file */
export const uriAtom = atom(get => get(modelAtom)?.uri)

/** The currently used RPC session */
export const currentRpcSessionAtom = atom<RpcSessionAtPos>()

/** The editor powering the typewriter (single line) input */
export const oneLineEditorAtom = atom<editor.IStandaloneCodeEditor | null>(null)

/** The analysied proof, received over RPC  */
export const proofQueryAtom = atomWithQuery<ProofState>((get) => {
  const worldId = get(worldIdAtom)
  const levelId = get(levelIdAtom)
  const code = get(codeStorageAtom)
  const rpcSess = get(currentRpcSessionAtom)
  return {
    queryKey: ['proof', worldId, levelId, rpcSess?.sessionId, code],
    queryFn: async () => {
      if (!rpcSess) return undefined
      const res = await rpcSess.client.sendRequest(
        '$/lean/rpc/call',
        {
          method: "Game.getProofState",
          params: {
            textDocument: {uri: rpcSess.uri},
            position: {line: 0, character: 0},
            worldId,
            levelId,
          },
          textDocument: {uri: rpcSess.uri},
          position: {line: 0, character: 0},
          sessionId: rpcSess.sessionId
        }
      )
      return res
    },
    enabled: rpcSess?.sessionId != undefined && code != undefined && worldId != undefined && levelId != undefined
  }
})

/**
 * The proof consists of multiple steps that are processed one after the other.
 * In particular multi-line terms like `match`-statements will not be supported.
 *
 * Note that the first step will always have "" as command
 */
export const proofAtom = atom(get => get(proofQueryAtom).data)












/*
I went up the dependency graph starting from the former
info.tsx  -> infos.ts -> main.tsx -> level.tsx -> index.tsx and extracted
contexts by their respective atoms. Some of the atoms do not belong here
and have been put here temporarly during my refactoring attempts.
*/

export const leanFileProgressAtom = atom<Map<string, LeanFileProgressProcessingInfo[]>>(new Map())

export const lspDiagnosticsAtom = atom<Map<DocumentUri, Diagnostic[]>>(new Map());

// export const serverVersionAtom = atom<ServerVersion>(new ServerVersion(''))

export const infoviewConfigAtom = atom<InfoviewConfig>(defaultInfoviewConfig)

// export const editorConnectionAtom = atom<EditorConnection | null>(null)



// export const rpcSessionsAtom = atom<RpcSessions | null>(null)

// export const rpcSessionAtPosAtom = atom<RpcSessionAtPos | null>(null)

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
    const editor = get(editorAtom)
    return editor?.getModel()
  }
)

export const leanMonacoEditorUriAtom = atom(
  (get) => {
    const model = get(leanMonacoEditorModelAtom)
    return model?.uri.toString() ?? ''
  }
)

export const haseditorAtom = atom(
  (get) => {
    const editor = get(editorAtom)
    console.log(`haseditorAtom: editor state is ${editor}`)
    const model = get(leanMonacoEditorModelAtom)
    console.log(`haseditorAtom: model state is ${model}`)
    return Boolean(editor && model)
  })

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
    const editor = get(editorAtom)
    const hasEditor = get(haseditorAtom)
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

    const hasEditor = get(haseditorAtom)
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
      console.log("[runCommand] start executing edits")
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
