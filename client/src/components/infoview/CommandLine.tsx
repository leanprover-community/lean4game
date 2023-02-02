import * as React from 'react'
import { useRef, useState } from 'react'
import { LspDiagnosticsContext } from '../../../../node_modules/lean4-infoview/src/infoview/contexts';
import { useServerNotificationEffect } from '../../../../node_modules/lean4-infoview/src/infoview/util';
import * as monaco from 'monaco-editor/esm/vs/editor/editor.api.js'
import { DiagnosticSeverity, PublishDiagnosticsParams } from 'vscode-languageserver-protocol';
import { InputModeContext, MonacoEditorContext } from '../Level'

import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faWandMagicSparkles } from '@fortawesome/free-solid-svg-icons'


function hasErrorsOrWarnings(diags) {
  return diags.some(
    (d) =>
      !d.message.startsWith("unsolved goals") &&
      (d.severity == DiagnosticSeverity.Error || d.severity == DiagnosticSeverity.Warning)
  )
}

export function CommandLine() {

  const editor = React.useContext(MonacoEditorContext)
  const commandInput = useRef<HTMLInputElement>()
  const [processing, setProcessing] = useState(false)

  const { commandLineMode } = React.useContext(InputModeContext)
  const allDiags = React.useContext(LspDiagnosticsContext)
  const diags = allDiags.get(editor.getModel().uri.toString())

  React.useEffect(() => {
    if (commandLineMode) {
      const endPos = editor.getModel().getFullModelRange().getEndPosition()
      if (editor.getModel().getLineContent(endPos.lineNumber).trim() !== "") {
        editor.executeEdits("command-line", [{
          range: monaco.Selection.fromPositions(endPos, endPos),
          text: "\n",
          forceMoveMarkers: false
        }]);
      }
      editor.setPosition(editor.getModel().getFullModelRange().getEndPosition())
    }
  }, [commandLineMode])

  const handleSubmit : React.FormEventHandler<HTMLFormElement> = (ev) => {
    ev.preventDefault()
    const pos = editor.getPosition()
    editor.executeEdits("command-line", [{
      range: monaco.Selection.fromPositions(
        pos,
        editor.getModel().getFullModelRange().getEndPosition()
      ),
      text: commandInput.current!.value + "\n",
      forceMoveMarkers: false
    }]);
    editor.setPosition(pos)
    setProcessing(true)
  }

  useServerNotificationEffect('textDocument/publishDiagnostics', (params: PublishDiagnosticsParams) => {
    if (params.uri == editor.getModel().uri.toString()) {
      setProcessing(false)
      if (!hasErrorsOrWarnings(params.diagnostics)) {
        commandInput.current!.value = "";
        editor.setPosition(editor.getModel().getFullModelRange().getEndPosition())
      }
    }
  }, []);

  return <div className="command-line">
      <form onSubmit={handleSubmit}>
        <input type="text" ref={commandInput} disabled={processing} />
        <button type="submit" disabled={processing} className="btn btn-inverted"><FontAwesomeIcon icon={faWandMagicSparkles} /> Run</button>
      </form>
    </div>
}
