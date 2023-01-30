import * as React from 'react'
import { useRef, useState } from 'react'
import { LspDiagnosticsContext } from '../../../../node_modules/lean4-infoview/src/infoview/contexts';
import { useServerNotificationEffect } from '../../../../node_modules/lean4-infoview/src/infoview/util';
import * as monaco from 'monaco-editor/esm/vs/editor/editor.api.js'
import { DiagnosticSeverity, PublishDiagnosticsParams } from 'vscode-languageserver-protocol';
import { MonacoEditorContext } from '../Level'

import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faWandMagicSparkles } from '@fortawesome/free-solid-svg-icons'


export function CommandLine() {

  const editor = React.useContext(MonacoEditorContext)
  const commandInput = useRef<HTMLInputElement>()
  const [processing, setProcessing] = useState(false)

  // const allDiags = React.useContext(LspDiagnosticsContext)
  // const fileDiags = allDiags.get(editor.getModel().uri.toString())


  const handleSubmit : React.FormEventHandler<HTMLFormElement> = (ev) => {
    ev.preventDefault()
    var selection = monaco.Selection.fromPositions(
      editor.getPosition(),
      editor.getModel().getFullModelRange().getEndPosition()
    );
    var text = commandInput.current!.value + "\n";
    var op = {range: selection, text: text, forceMoveMarkers: false};
    editor.executeEdits("my-source", [op], editor.getSelections());
    setProcessing(true)
  }

  useServerNotificationEffect('textDocument/publishDiagnostics', (params: PublishDiagnosticsParams) => {
    if (params.uri == editor.getModel().uri.toString()) {
      setProcessing(false)
      const hasErrorsOrWarnings = params.diagnostics.some(
        (d) =>
          !d.message.startsWith("unsolved goals") &&
          (d.severity == DiagnosticSeverity.Error || d.severity == DiagnosticSeverity.Warning)
      )
      if (!hasErrorsOrWarnings) {
        commandInput.current!.value = "";
        editor.setPosition(editor.getModel().getFullModelRange().getEndPosition())
      }
    }
  }, []);

  return <div className="command-line">
      <form onSubmit={handleSubmit}>
        <input type="text" ref={commandInput} disabled={processing} />
        <button type="submit" disabled={processing} className="btn"><FontAwesomeIcon icon={faWandMagicSparkles} /> Run</button>
      </form>
    </div>
}
