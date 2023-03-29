import * as React from 'react'
import { useRef, useState, useEffect } from 'react'
import { LspDiagnosticsContext } from '../../../../node_modules/lean4-infoview/src/infoview/contexts';
import { useServerNotificationEffect } from '../../../../node_modules/lean4-infoview/src/infoview/util';
import * as monaco from 'monaco-editor/esm/vs/editor/editor.api.js'
import { DiagnosticSeverity, PublishDiagnosticsParams } from 'vscode-languageserver-protocol';
import { InputModeContext, MonacoEditorContext } from '../Level'

import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faWandMagicSparkles } from '@fortawesome/free-solid-svg-icons'
import { AbbreviationRewriter } from 'lean4web/client/src/editor/abbreviation/rewriter/AbbreviationRewriter';
import { AbbreviationProvider } from 'lean4web/client/src/editor/abbreviation/AbbreviationProvider';

import { Registry } from 'monaco-textmate' // peer dependency
import { wireTmGrammars } from 'monaco-editor-textmate'
import * as lightPlusTheme from 'lean4web/client/src/lightPlus.json'
import * as leanSyntax from 'lean4web/client/src/syntaxes/lean.json'
import * as leanMarkdownSyntax from 'lean4web/client/src/syntaxes/lean-markdown.json'
import * as codeblockSyntax from 'lean4web/client/src/syntaxes/codeblock.json'
import languageConfig from 'lean4/language-configuration.json';


/* We register a new language `leancmd` that looks like lean4, but does not use the lsp server. */

// register Monaco languages
monaco.languages.register({
  id: 'lean4cmd',
  extensions: ['.leancmd']
})

// map of monaco "language id's" to TextMate scopeNames
const grammars = new Map()
grammars.set('lean4', 'source.lean')
grammars.set('lean4cmd', 'source.lean')

const registry = new Registry({
  getGrammarDefinition: async (scopeName) => {
    if (scopeName === 'source.lean') {
      return {
          format: 'json',
          content: JSON.stringify(leanSyntax)
      }
    } else if (scopeName === 'source.lean.markdown') {
      return {
          format: 'json',
          content: JSON.stringify(leanMarkdownSyntax)
      }
    } else {
      return {
          format: 'json',
          content: JSON.stringify(codeblockSyntax)
      }
    }
  }
});

wireTmGrammars(monaco, registry, grammars)

let config: any = { ...languageConfig }
config.autoClosingPairs = config.autoClosingPairs.map(
  pair => { return {'open': pair[0], 'close': pair[1]} }
)
monaco.languages.setLanguageConfiguration('lean4cmd', config);

export function CommandLine() {

  /** Reference to the hidden multi-line editor */
  const editor = React.useContext(MonacoEditorContext)
  const [oneLineEditor, setOneLineEditor] = useState<monaco.editor.IStandaloneCodeEditor>(null)
  const [processing, setProcessing] = useState(false)

  const { commandLineMode, commandLineInput, setCommandLineInput } = React.useContext(InputModeContext)

  const inputRef = useRef()

  // Run the command
  const runCommand = React.useCallback(() => {
    if (processing) return;
    const pos = editor.getPosition()
    editor.executeEdits("command-line", [{
      range: monaco.Selection.fromPositions(
        pos,
        editor.getModel().getFullModelRange().getEndPosition()
      ),
      text: commandLineInput + "\n",
      forceMoveMarkers: false
    }]);
    editor.setPosition(pos)
    setProcessing(true)
  }, [commandLineInput, editor])

  useEffect(() => {
    if (oneLineEditor && oneLineEditor.getValue() !== commandLineInput) {
      oneLineEditor.setValue(commandLineInput)
    }
  }, [commandLineInput])

  // React when answer from the server comes back
  useServerNotificationEffect('textDocument/publishDiagnostics', (params: PublishDiagnosticsParams) => {
    if (params.uri == editor.getModel().uri.toString()) {
      setProcessing(false)
      if (!hasErrorsOrWarnings(params.diagnostics)) {
        setCommandLineInput("")
        editor.setPosition(editor.getModel().getFullModelRange().getEndPosition())
      }
    }
  }, []);

  useEffect(() => {
    const myEditor = monaco.editor.create(inputRef.current!, {
      value: commandLineInput,
      language: "lean4cmd",
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
      lineDecorationsWidth: 0,
      lineNumbersMinChars: 0,
      'semanticHighlighting.enabled': true,
      overviewRulerLanes: 0,
      hideCursorInOverviewRuler: true,
      scrollbar: {
        vertical: 'hidden',
        horizontalScrollbarSize: 3
      },
      overviewRulerBorder: false,
      theme: 'vs-code-theme-converted',
      contextmenu: false
    })

    setOneLineEditor(myEditor)

    const abbrevRewriter = new AbbreviationRewriter(new AbbreviationProvider(), myEditor.getModel(), myEditor)

    return () => {abbrevRewriter.dispose(); myEditor.dispose()}
  }, [])

  useEffect(() => {
    if (!oneLineEditor) return
    // Ensure that our one-line editor can only have a single line
    const l = oneLineEditor.getModel().onDidChangeContent((e) => {
      const value = oneLineEditor.getValue()
      setCommandLineInput(value)
      const newValue = value.replace(/[\n\r]/g, '')
      if (value != newValue) {
        oneLineEditor.setValue(newValue)
      }
    })
    return () => { l.dispose() }
  }, [oneLineEditor, setCommandLineInput])

  useEffect(() => {
    if (!oneLineEditor) return
    // Run command when pressing enter
    const l = oneLineEditor.onKeyUp((ev) => {
      if (ev.code === "Enter") {
        runCommand()
      }
    })
    return () => { l.dispose() }
  }, [oneLineEditor, runCommand])

  const handleSubmit : React.FormEventHandler<HTMLFormElement> = (ev) => {
    ev.preventDefault()
    runCommand()
  }

  return <div className="command-line">
      <form onSubmit={handleSubmit}>
        <div className="command-line-input-wrapper">
          <div ref={inputRef} className="command-line-input" />
        </div>
        <button type="submit" disabled={processing} className="btn btn-inverted"><FontAwesomeIcon icon={faWandMagicSparkles} /> Execute</button>
      </form>
    </div>
}

/** Checks whether the diagnostics contain any errors or warnings to check whether the level has
   been completed.*/
function hasErrorsOrWarnings(diags) {
  return diags.some(
    (d) =>
      !d.message.startsWith("unsolved goals") &&
      (d.severity == DiagnosticSeverity.Error || d.severity == DiagnosticSeverity.Warning)
  )
}
