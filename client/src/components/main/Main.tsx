// TODO: This is only used in `EditorInterface`

import { useTranslation } from "react-i18next";
import { useGameTranslation } from "../../utils/translation";
import { crashedAtom, lockEditorModeAtom, proofAtom, typewriterModeAtom } from "../../store/editor-atoms";
import { useAtom } from "jotai";
import React from "react";
import { gameIdAtom, levelIdAtom, worldIdAtom } from "../../store/location-atoms";
import { gameInfoAtom, levelInfoAtom } from "../../store/query-atoms";
import { helpAtom, selectedStepAtom } from "../../store/chat-atoms";
import { useRpcSessionAtPos } from "lean4monaco/dist/vscode-lean4/lean4-infoview/src/infoview/rpcSessions";
import { loadGoals } from "../../../../infoview/goals";
import { useEventResult } from "../infoview/editor/util";
import { useServerNotificationState } from "lean4monaco/dist/vscode-lean4/lean4-infoview/src/infoview/util";

// TODO: This is only used in `EditorInterface`
// while `TypewriterInterface` has this copy-pasted in.
export function Main() {
  let { t } = useTranslation()
  const { t: gT } = useGameTranslation()
  const [lockEditorMode] = useAtom(lockEditorModeAtom)
  const ec = React.useContext(EditorContext);
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
  const editor = React.useContext(MonacoEditorContext)
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
  const config = useEventResult(ec.events.changedInfoviewConfig) ?? defaultInfoviewConfig;

  const [allProgress, _1] = useServerNotificationState(
    '$/lean/fileProgress',
    new Map<DocumentUri, LeanFileProgressProcessingInfo[]>(),
    async (params: LeanFileProgressParams) => (allProgress) => {
      const newProgress = new Map(allProgress);
      return newProgress.set(params.textDocument.uri, params.processing);
    },
    []
  );

  const curUri = useEventResult(ec.events.changedCursorLocation, loc => loc?.uri);

  const curPos: DocumentPosition | undefined =
    useEventResult(ec.events.changedCursorLocation, loc => loc ? { uri: loc.uri, ...loc.range.start } : undefined)

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
      ? curPos.character
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
    return proof.steps[hintStepIndex]?.goals?.[0]?.hints
  })()

  // Effect when the cursor changes in the editor
  React.useEffect(() => {
    // TODO: this is a bit of a hack and will yield unexpected behaviour if lines
    // are indented.
    const newPos = curPos?.line + (curPos?.character == 0 ? 0 : 1)

    if (Number.isFinite(newPos)) {
      // scroll the chat along
      setSelectedStep(newPos)
    }
  }, [curPos])

  useClientNotificationEffect(
    'textDocument/didClose',
    (params: DidCloseTextDocumentParams) => {
      if (ec.events.changedCursorLocation.current &&
        ec.events.changedCursorLocation.current.uri === params.textDocument.uri) {
        ec.events.changedCursorLocation.fire(undefined)
      }
    },
    []
  );

  const serverVersion =
    useEventResult(ec.events.serverRestarted, result => new ServerVersion(result.serverInfo?.version ?? ''))
  const serverStoppedResult = useEventResult(ec.events.serverStopped);
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
        <Infos />
      </div>
      {hintsToShow && (
        <Hints hints={hintsToShow}
          showHidden={help.has(hintStepIndex)} step={hintStepIndex}
          selected={selectedStep} toggleSelection={toggleSelection(hintStepIndex)}
          lastLevel={hintStepIndex == proof?.steps.length - 1}/>
      )}
      <MoreHelpButton selected={curPos?.line}/>
    </div>
  }

  return ret
}
