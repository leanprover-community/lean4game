import React from "react";
import { TypewriterInterface } from "./TypewriterInterface";
import { useClientNotificationEffect, useEventResult } from "lean4monaco/dist/vscode-lean4/lean4-infoview/src/infoview/util";
import { ServerVersion } from 'lean4monaco/dist/vscode-lean4/lean4-infoview/src/infoview/serverVersion';
import type { DidCloseTextDocumentParams, DocumentUri } from 'vscode-languageserver-protocol';
import { useAtom } from "jotai";
import { editorConnectionAtom } from "../../store/editor-atoms";

// Splitting up Typewriter into two parts is a HACK
export function TypewriterInterfaceWrapper() {
  const [editorConnection, _] = useAtom(editorConnectionAtom)//React.useContext(EditorContext)

  useClientNotificationEffect(
    'textDocument/didClose',
    (params: DidCloseTextDocumentParams) => {
      if (editorConnection!.events.changedCursorLocation.current &&
        editorConnection!.events.changedCursorLocation.current.uri === params.textDocument.uri) {
        editorConnection!.events.changedCursorLocation.fire(undefined)
      }
    }, []
  )

  const serverVersion =
    useEventResult(editorConnection!.events.serverRestarted, result => new ServerVersion(result.serverInfo?.version ?? ''))
  const serverStoppedResult = useEventResult(editorConnection!.events.serverStopped);
  // NB: the cursor may temporarily become `undefined` when a file is closed. In this case
  // it's important not to reconstruct the `WithBlah` wrappers below since they contain state
  // that we want to persist.

  if (serverStoppedResult) {
    return <div>
      <p>{serverStoppedResult.message}</p>
      <p className="error">{serverStoppedResult.reason}</p>
    </div>
  }

  return <TypewriterInterface />
}
