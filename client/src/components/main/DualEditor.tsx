import { useAtom } from "jotai"
import { editorConnectionAtom, infoviewConfigAtom, leanFileProgressAtom, lspDiagnosticsAtom, proofAtom, rpcSessionsAtom, serverVersionAtom, typewriterModeAtom } from "../../store/editor-atoms"
import React from "react"
import { ExerciseStatement } from "../infoview/ExerciseStatement"
import { gameIdAtom, levelIdAtom, worldIdAtom } from "../../store/location-atoms"
import { gameInfoAtom, levelInfoAtom } from "../../store/query-atoms"
import { completedAtom, progressAtom } from "../../store/progress-atoms"
import { inventoryAtom } from "../../store/inventory-atoms"
import { TypewriterInterfaceWrapper } from "./TypewriterInterfaceWrapper"
import { Main } from "./Main"
import { useClientNotificationEffect, useEvent, useEventResult, useServerNotificationState } from "lean4monaco/dist/vscode-lean4/lean4-infoview/src/infoview/util"
import type { Diagnostic, DidCloseTextDocumentParams, DocumentUri, PublishDiagnosticsParams } from 'vscode-languageserver-protocol';
import { LeanFileProgressParams, LeanFileProgressProcessingInfo, RpcCallParams, defaultInfoviewConfig } from '@leanprover/infoview-api';
import { ServerVersion }  from 'lean4monaco/dist/vscode-lean4/lean4-infoview/src/infoview/serverVersion'
import { RpcSessionAtPos, RpcSessions } from 'lean4monaco/dist/vscode-lean4/lean4-infoview-api/src/rpcSessions'
import { RpcReleaseParams } from "lean4monaco/dist/vscode-lean4/lean4-infoview-api/src/lspTypes"



/** Wrapper for the two editors. It is important that the `div` with `codeViewRef` is
 * always present, or the monaco editor cannot start.
 */
export function DualEditor({ codeviewRef } : { codeviewRef: any }) {
  const [typewriterMode] = useAtom(typewriterModeAtom)
  const ec = useAtom(editorConnectionAtom)//React.useContext(EditorContext)
  const showTypewriter = Boolean(ec) && typewriterMode
  return <>
    <div className={showTypewriter ? 'hidden' : ''}>
      <ExerciseStatement showLeanStatement={true} />
      <div ref={codeviewRef} className={'codeview'}></div>
    </div>
    {ec ?
      <DualEditorMain /> :
      // TODO: Style this if relevant.
      <></>
    }
  </>
}

/** The part of the two editors that needs the editor connection first */
function DualEditorMain() {
  const [editorConnection,] = useAtom(editorConnectionAtom)//React.useContext(EditorContext)
  const [rpcSessions, setRpcSessions] = useAtom(rpcSessionsAtom)
  const [, setServerVersion] = useAtom(serverVersionAtom)
  const [, setInfoviewConfig] = useAtom(infoviewConfigAtom)
  const [, setLspDiagnostics] = useAtom(lspDiagnosticsAtom)
  const [, setLeanFileProgressAtom] = useAtom(leanFileProgressAtom)
  const [gameId] = useAtom(gameIdAtom)
  const [worldId] = useAtom(worldIdAtom)
  const [levelId] = useAtom(levelIdAtom)
  const [{ data: gameInfo }] = useAtom(gameInfoAtom)
  const [{ data: levelInfo }] = useAtom(levelInfoAtom)

  const [, setCompleted] = useAtom(completedAtom)

  const [, addToInventory] = useAtom(inventoryAtom)
  const [typewriterMode, setTypewriterMode] = useAtom(typewriterModeAtom)

  const [proof] = useAtom(proofAtom)

  // REPLACES WithRpcSessions
  // Initialize RpcSessions when editorConnection is available
  React.useEffect(() => {
    if (!editorConnection) {
      console.log("[DualEditorMain] No editor connection available during RPC sesssion creation.")
      return;
    }

    const sessions = new RpcSessions({
      createRpcSession: (uri: DocumentUri) => editorConnection.api.createRpcSession(uri),
      closeRpcSession: (uri: DocumentUri) => editorConnection.api.closeRpcSession(uri),
      call: (params: RpcCallParams) => editorConnection.api.sendClientRequest(params.textDocument.uri, '$/lean/rpc/call', params),
      release: (params: RpcReleaseParams) => editorConnection.api.sendClientNotification(params.uri, '$/lean/rpc/release', params),
    });

    setRpcSessions(sessions);

    // Clean up the sessions on unmount
    return () => sessions.dispose();
  }, [editorConnection, setRpcSessions]);

  React.useEffect(() => {
    if (proof?.completed) {
      setCompleted(true)

      // On completion, add the names of all new items to the local storage
      let newTiles = [
        ...levelInfo?.tactics ?? [],
        ...levelInfo?.lemmas ?? [],
        ...levelInfo?.definitions ?? []
      ].filter((tile) => tile.new).map((tile) => tile.name)

      // Add the proven statement to the local storage as well.
      if (levelInfo?.statementName != null) {
        newTiles.push(levelInfo?.statementName)
      }
      addToInventory(newTiles)
    }
  }, [proof, levelInfo])

  // REPLACES the ConfigContext
  /* Set up updates to the global infoview state on editor events. */
  React.useEffect(() => {
    if (!editorConnection) {
      console.log("[DualEditorMain] No editor connection available during InfoviewConfig creation.")
      return;
    }

    // The value for the messageOrder had to be copied from @leanprovers definition.
    // This is needed, because EditorConnection is imported from lean4monaco where the
    // the definition for the InfoViewConfig does not contain messageOrder.
    // This is a symptom of several dependency crashed that need to be addressed at some point.
    const unsubscribe = editorConnection.events.changedInfoviewConfig.on((config) => {
      setInfoviewConfig({...config, messageOrder: 'Sort by proximity to text cursor'})
    });

    // Clean up the subscription on unmount
    return () => unsubscribe?.dispose();
  }, [editorConnection, setInfoviewConfig]);

  // REPLACES the VersionContext
  // Update the server version whenever the server restarts
  React.useEffect(() => {
    if (!editorConnection) return;

    const unsubscribeServer = editorConnection.events.serverRestarted.on((result) => {
      setServerVersion(new ServerVersion(result.serverInfo?.version ?? ''));
    });

    return () => unsubscribeServer?.dispose();
  }, [editorConnection, setServerVersion]);

  // Handle closing sessions for closed files
  useClientNotificationEffect(
    'textDocument/didClose',
    (params: DidCloseTextDocumentParams) => {
      const [rpcSessions] = useAtom(rpcSessionsAtom);
      rpcSessions?.closeSessionForFile(params.textDocument.uri);
    },
    [],
  );

  // REPLACES the WithLspDiagnosticsContext
  // Update the LSP diagnostics whenever the notification is received
  useServerNotificationState(
    'textDocument/publishDiagnostics',
    new Map<DocumentUri, Diagnostic[]>(),
    async (params: PublishDiagnosticsParams) => (diags) => {
      const newDiags = new Map(diags);
      newDiags.set(params.uri, params.diagnostics);
      setLspDiagnostics(newDiags);
      return newDiags;
    },
    []
  );

  // REPLACES the ProgressContext
  const [allProgress, _1] = useServerNotificationState(
    '$/lean/fileProgress',
    new Map<DocumentUri, LeanFileProgressProcessingInfo[]>(),
    async (params: LeanFileProgressParams) => (allProgress) => {
      const newProgress = new Map(allProgress);
      newProgress.set(params.textDocument.uri, params.processing);
      setLeanFileProgressAtom(newProgress)
      return newProgress
    }, [])

  // Handle server restart
  useEvent(editorConnection!.events.serverRestarted, () => {
    rpcSessions?.closeAllSessions();
  });

  return <>
  {(typewriterMode) ?
    <TypewriterInterfaceWrapper/>
    :
    <Main key={`${worldId}/${levelId}`} />
  }
  </>
}
