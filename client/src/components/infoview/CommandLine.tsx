import * as React from 'react'
import { useRef, useState, useEffect } from 'react'
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

  const inputRef = useRef()

  useEffect(() => {
    const editor = monaco.editor.create(inputRef.current!, {
      quickSuggestions: false,
      lightbulb: {
        enabled: true
      },
      unicodeHighlight: {
          ambiguousCharacters: false,
      },
      automaticLayout: true,
      minimap: {
        enabled: false
      },
      lineNumbers: 'off',
      glyphMargin: false,
      folding: false,
      // Undocumented see https://github.com/Microsoft/vscode/issues/30795#issuecomment-410998882
      lineDecorationsWidth: 0,
      lineNumbersMinChars: 0,
      'semanticHighlighting.enabled': true,
      overviewRulerLanes: 0,
      hideCursorInOverviewRuler: true,
      scrollbar: {
          vertical: 'hidden'
      },
      overviewRulerBorder: false,
      theme: 'vs-code-theme-converted',
      contextmenu: false
    })

    const t = editor.getModel().onDidChangeContent((e) => {
      const value = editor.getValue()
      const newValue = value.replace(/[\n\r]/g, '')
      if (value != newValue) {
        editor.setValue(newValue)
      }
    })

    return () => {t.dispose(); editor.dispose()}
  }, [])

  // Effect when command line mode gets enabled
  useEffect(() => {
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

  // Run the command
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

  // React when answer from the server comes back
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
        <div ref={inputRef} className="command-line-input" />
        {/* <input type="text" ref={commandInput} disabled={processing} /> */}
        <button type="submit" disabled={processing} className="btn btn-inverted"><FontAwesomeIcon icon={faWandMagicSparkles} /> Run</button>
      </form>
    </div>
}
