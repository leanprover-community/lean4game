// TODO: This is only used in `EditorInterface`

import { useTranslation } from "react-i18next";
import { useGameTranslation } from "../../utils/translation";
import { crashedAtom, editorConnectionAtom, editorAtom, lockEditorModeAtom, proofAtom, serverVersionAtom, typewriterModeAtom } from "../../store/editor-atoms";
import { useAtom } from "jotai";
import React from "react";
import { gameIdAtom, levelIdAtom, worldIdAtom } from "../../store/location-atoms";
import { gameInfoAtom, levelInfoAtom } from "../../store/query-atoms";
import { helpAtom, selectedStepAtom } from "../../store/chat-atoms";
import { useRpcSessionAtPos } from "lean4monaco/dist/vscode-lean4/lean4-infoview/src/infoview/rpcSessions";
import { lastStepHasErrors, loadGoals } from "../../../../infoview/goals";
import { DocumentPosition } from "../infoview/editor/util";
import { useServerNotificationEffect, useServerNotificationState, useEventResult, useClientNotificationEffect } from "lean4monaco/dist/vscode-lean4/lean4-infoview/src/infoview/util";
import { defaultInfoviewConfig, LeanFileProgressParams, LeanFileProgressProcessingInfo } from "@leanprover/infoview-api";
import type { DidCloseTextDocumentParams, DocumentUri } from 'vscode-languageserver-protocol'
import { ServerVersion } from "lean4monaco/dist/vscode-lean4/lean4-infoview/src/infoview/serverVersion";
import { Hints } from "../hints";

// TODO: This is only used in `EditorInterface`
// while `TypewriterInterface` has this copy-pasted in.
export function Main() {
  let { t } = useTranslation()
  const { t: gT } = useGameTranslation()
  const [lockEditorMode] = useAtom(lockEditorModeAtom)
  const [editorConnection,] = useAtom(editorConnectionAtom)//React.useContext(EditorContext);
  const [gameId] = useAtom(gameIdAtom)
  const [worldId] = useAtom(worldIdAtom)
  const [levelId] = useAtom(levelIdAtom)
  const [{ data: gameInfo }] = useAtom(gameInfoAtom)
  const [{ data: levelInfo }] = useAtom(levelInfoAtom)
  const [help, setHelp] = useAtom(helpAtom)

  const [typewriterMode] = useAtom(typewriterModeAtom)

  const [proof, setProof] = useAtom(proofAtom)
  const [, setCrashed] = useAtom(crashedAtom)
  const [selectedStep, setSelectedStep] = useAtom(selectedStepAtom)
  const [editor,] = useAtom(editorAtom)//React.useContext(MonacoEditorContext)
  const [, setServerVersion] = useAtom(serverVersionAtom)
  const model = editor?.getModel()
  const uri = model?.uri.toString()
  const rpcSess = useRpcSessionAtPos({ uri: uri ?? '', line: 0, character: 0 })

  React.useEffect(() => {
    if (!uri || !worldId || !levelId) {
      return
    }
    loadGoals(rpcSess, uri, worldId, levelId, setProof, setCrashed)
  }, [rpcSess, uri, worldId, levelId, setProof, setCrashed])

  function toggleSelection(line: number) {
    return (ev: any) => {
      console.debug('toggled selection')
      if (selectedStep == line) {
        setSelectedStep(undefined)
      } else {
        setSelectedStep(line)
      }
    }
  }
  //console.debug(`template: ${props.data?.template}`)

  // React.useEffect (() => {
  //   if (props.data.template) {
  //     let code: string = selectCode(gameId, worldId, levelId)(store.getState())
  //     if (!code.length) {
  //       //models.push(monaco.editor.createModel(code, 'lean4', uri))
  //     }
  //   }
  // }, [props.data.template])

  /* Set up updates to the global infoview state on editor events. */
  // config is not used
  //const config = useEventResult(editorConnection!.events.changedInfoviewConfig) ?? defaultInfoviewConfig;

  const [allProgress, _1] = useServerNotificationState(
    '$/lean/fileProgress',
    new Map<DocumentUri, LeanFileProgressProcessingInfo[]>(),
    async (params: LeanFileProgressParams) => (allProgress) => {
      const newProgress = new Map(allProgress);
      return newProgress.set(params.textDocument.uri, params.processing);
    },
    []
  );

  // curUri is not used
  //const curUri = useEventResult(editorConnection.events.changedCursorLocation, loc => loc?.uri);

  const curPos: DocumentPosition | undefined =
    useEventResult(
      editorConnection!.events.changedCursorLocation,
      loc => loc ? { uri: loc.uri, ...loc.range.start } : undefined)

  React.useEffect(() => {
    if (typewriterMode) {
      return
    }
    if (!uri) {
      return
    }
    loadGoals(rpcSess, uri, worldId!, levelId!, setProof, setCrashed)
  }, [typewriterMode, lockEditorMode, uri, worldId, levelId, rpcSess, setProof, setCrashed])

  useServerNotificationEffect('textDocument/publishDiagnostics', (params: any) => {
    if (typewriterMode) {
      return
    }
    if (!uri || params?.uri !== uri) {
      return
    }
    loadGoals(rpcSess, uri, worldId!, levelId!, setProof, setCrashed)
  }, [typewriterMode, lockEditorMode, uri, worldId, levelId, rpcSess, setProof, setCrashed])

  const hintLine = (() => {
    const isEditorMode = !(typewriterMode)
    const curLine = Number.isFinite(curPos?.line)
      ? curPos?.line
      : (Number.isFinite((curPos as any)?._line) ? (curPos as any)._line : undefined)
    const curChar = Number.isFinite(curPos?.character)
      ? curPos?.character
      : (Number.isFinite((curPos as any)?._character) ? (curPos as any)._character : undefined)
    if (isEditorMode && Number.isFinite(curLine)) {
      const baseLine = curLine
      return (curChar === 0 && baseLine > 0) ? baseLine - 1 : baseLine
    }
    if (Number.isFinite(selectedStep)) {
      return selectedStep
    }
    if (!proof?.steps?.length) {
      return 0
    }
    const lastIndex = proof.steps.length - 1
    return lastStepHasErrors(proof) ? Math.max(0, lastIndex - 1) : lastIndex
  })()

  const clampedHintLine = Math.max(0, Math.min(Number.isFinite(hintLine) ? hintLine : 0, (proof?.steps?.length ?? 1) - 1))

  const hintStepIndex = (() => {
    if (Number.isFinite(selectedStep)) {
      return selectedStep
    }
    if (!proof?.steps?.length) {
      return 0
    }
    const maxIndex = proof.steps.length - 1
    return Math.min(clampedHintLine + 1, maxIndex)
  })()

  const hintsToShow = (() => {
    if (!proof?.steps?.length) {
      return undefined
    }
    return proof.steps[hintStepIndex!]?.goals?.[0]?.hints
  })()

  // Effect when the cursor changes in the editor
  React.useEffect(() => {
    // TODO: this is a bit of a hack and will yield unexpected behaviour if lines
    // are indented.
    const newPos = curPos!.line + (curPos?.character == 0 ? 0 : 1)

    if (Number.isFinite(newPos)) {
      // scroll the chat along
      setSelectedStep(newPos)
    }
  }, [curPos])

  useClientNotificationEffect(
    'textDocument/didClose',
    (params: DidCloseTextDocumentParams) => {
      if (editorConnection!.events.changedCursorLocation.current &&
        editorConnection!.events.changedCursorLocation.current.uri === params.textDocument.uri) {
        editorConnection!.events.changedCursorLocation.fire(undefined)
      }
    },
    []
  );

  // serverVersion has to be given to what was former the version context
  const serverVersion = useEventResult(editorConnection!.events.serverRestarted, result => new ServerVersion(result.serverInfo?.version ?? ''))

  console.log(`server version: ${serverVersion}`)

  setServerVersion(serverVersion!)

  const serverStoppedResult = useEventResult(editorConnection!.events.serverStopped);
  // NB: the cursor may temporarily become `undefined` when a file is closed. In this case
  // it's important not to reconstruct the `WithBlah` wrappers below since they contain state
  // that we want to persist.
  let ret
  if (serverStoppedResult) {
    ret = <div><p>{serverStoppedResult.message}</p><p className="error">{serverStoppedResult.reason}</p></div>
  } else {
    ret = <div className="infoview vscode-light">
      <div className="lean4game-infoview">
        {proof?.completedWithWarnings &&
          <div className="level-completed">
            {proof?.completed ? t("Level completed! 🎉") : t("Level completed with warnings 🎭")}
          </div>
        }
        {/* <Infos /> */}
      </div>
      {hintsToShow && (
        <Hints hints={hintsToShow}
          showHidden={help.has(hintStepIndex!)} step={hintStepIndex!}
          selected={selectedStep} toggleSelection={toggleSelection(hintStepIndex!)}
          lastLevel={hintStepIndex == proof!.steps.length - 1}/>
      )}
      {/* <MoreHelpButton selected={curPos?.line}/> */}
    </div>
  }

  return ret
}
