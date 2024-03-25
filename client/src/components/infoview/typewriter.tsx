import * as React from 'react'
import { useRef, useState, useEffect } from 'react'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faWandMagicSparkles } from '@fortawesome/free-solid-svg-icons'
import * as monaco from 'monaco-editor/esm/vs/editor/editor.api.js'
import { Registry } from 'monaco-textmate' // peer dependency
import { wireTmGrammars } from 'monaco-editor-textmate'
import { DiagnosticSeverity, PublishDiagnosticsParams, DocumentUri } from 'vscode-languageserver-protocol';
import { useServerNotificationEffect } from '../../../../node_modules/lean4-infoview/src/infoview/util';
import { AbbreviationRewriter } from 'lean4web/client/src/editor/abbreviation/rewriter/AbbreviationRewriter';
import { AbbreviationProvider } from 'lean4web/client/src/editor/abbreviation/AbbreviationProvider';
import * as leanSyntax from 'lean4web/client/src/syntaxes/lean.json'
import * as leanMarkdownSyntax from 'lean4web/client/src/syntaxes/lean-markdown.json'
import * as codeblockSyntax from 'lean4web/client/src/syntaxes/codeblock.json'
import languageConfig from 'lean4/language-configuration.json';
import { InteractiveDiagnostic, RpcSessionAtPos, getInteractiveDiagnostics } from '@leanprover/infoview-api';
import { Diagnostic } from 'vscode-languageserver-types';
import { DocumentPosition } from '../../../../node_modules/lean4-infoview/src/infoview/util';
import { RpcContext } from '../../../../node_modules/lean4-infoview/src/infoview/rpcSessions';
import { DeletedChatContext, InputModeContext, MonacoEditorContext, ProofContext } from './context'
import { goalsToString, lastStepHasErrors, loadGoals } from './goals'
import { GameHint, ProofState } from './rpc_api'
import { useTranslation } from 'react-i18next'

export interface GameDiagnosticsParams {
  uri: DocumentUri;
  diagnostics: Diagnostic[];
}

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

/** The input field */
export function Typewriter({disabled}: {disabled?: boolean}) {
  let { t } = useTranslation()

  /** Reference to the hidden multi-line editor */
  const editor = React.useContext(MonacoEditorContext)
  const model = editor.getModel()
  const uri = model.uri.toString()

  const [oneLineEditor, setOneLineEditor] = useState<monaco.editor.IStandaloneCodeEditor>(null)
  const [processing, setProcessing] = useState(false)

  const {typewriterInput, setTypewriterInput} = React.useContext(InputModeContext)

  const inputRef = useRef()

  // The context storing all information about the current proof
  const {proof, setProof, interimDiags, setInterimDiags, setCrashed} = React.useContext(ProofContext)

  // state to store the last batch of deleted messages
  const {setDeletedChat} = React.useContext(DeletedChatContext)

  const rpcSess = React.useContext(RpcContext)

  // Run the command
  const runCommand = React.useCallback(() => {
    if (processing) {return}

    // TODO: Desired logic is to only reset this after a new *error-free* command has been entered
    setDeletedChat([])

    const pos = editor.getPosition()
    if (typewriterInput) {
      setProcessing(true)
      editor.executeEdits("typewriter", [{
        range: monaco.Selection.fromPositions(
          pos,
          editor.getModel().getFullModelRange().getEndPosition()
        ),
        text: typewriterInput.trim() + "\n",
        forceMoveMarkers: false
      }])
      setTypewriterInput('')
      // Load proof after executing edits
      loadGoals(rpcSess, uri, setProof, setCrashed)
    }

    editor.setPosition(pos)
  }, [typewriterInput, editor])

  useEffect(() => {
    if (oneLineEditor && oneLineEditor.getValue() !== typewriterInput) {
      oneLineEditor.setValue(typewriterInput)
    }
  }, [typewriterInput])

  /* Load proof on start/switching to typewriter */
  useEffect(() => {
    loadGoals(rpcSess, uri, setProof, setCrashed)
  }, [])

  /** If the last step has an error, add the command to the typewriter. */
  useEffect(() => {
    if (lastStepHasErrors(proof)) {
      setTypewriterInput(proof?.steps[proof?.steps.length - 1].command)
    }
  }, [proof])

  // React when answer from the server comes back
  useServerNotificationEffect('textDocument/publishDiagnostics', (params: PublishDiagnosticsParams) => {
    if (params.uri == uri) {
      setProcessing(false)

      console.log('Received lean diagnostics')
      console.log(params.diagnostics)
      setInterimDiags(params.diagnostics)

      //loadGoals(rpcSess, uri, setProof)

      // TODO: loadAllGoals()
      if (!hasErrors(params.diagnostics)) {
        //setTypewriterInput("")
        editor.setPosition(editor.getModel().getFullModelRange().getEndPosition())
      }
    } else {
      // console.debug(`expected uri: ${uri}, got: ${params.uri}`)
      // console.debug(params)
    }
    // TODO: This is the wrong place apparently. Where do wee need to load them?
    // TODO: instead of loading all goals every time, we could only load the last one
    // loadAllGoals()
  }, [uri]);

  // // React when answer from the server comes back
  // useServerNotificationEffect('$/game/publishDiagnostics', (params: GameDiagnosticsParams) => {
  //   console.log('Received game diagnostics')
  //   console.log(`diag. uri : ${params.uri}`)
  //   console.log(params.diagnostics)

  // }, [uri]);


  useEffect(() => {
    const myEditor = monaco.editor.create(inputRef.current!, {
      value: typewriterInput,
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
      tabSize: 2,
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
      setTypewriterInput(value)
      const newValue = value.replace(/[\n\r]/g, '')
      if (value != newValue) {
        oneLineEditor.setValue(newValue)
      }
    })
    return () => { l.dispose() }
  }, [oneLineEditor, setTypewriterInput])

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

  // BUG: Causes `file closed` error
  //TODO: Intention is to run once when loading, does that work?
  useEffect(() => {
    console.debug(`time to update: ${uri} \n ${rpcSess}`)
    console.debug(rpcSess)
    // console.debug('LOAD ALL GOALS')
    // TODO: loadAllGoals()
  }, [rpcSess])

  /** Process the entered command */
  const handleSubmit : React.FormEventHandler<HTMLFormElement> = (ev) => {
    ev.preventDefault()
    runCommand()
  }

  // do not display if the proof is completed (with potential warnings still present)
  return <div className={`typewriter${proof?.completedWithWarnings ? ' hidden' : ''}${disabled ? ' disabled' : ''}`}>
      <form onSubmit={handleSubmit}>
        <div className="typewriter-input-wrapper">
          <div ref={inputRef} className="typewriter-input" />
        </div>
        <button type="submit" disabled={processing} className="btn btn-inverted">
          <FontAwesomeIcon icon={faWandMagicSparkles} />&nbsp;{t("Execute")}
        </button>
      </form>
    </div>
}

/** Checks whether the diagnostics contain any errors or warnings to check whether the level has
   been completed.*/
export function hasErrors(diags: Diagnostic[]) {
  return diags.some(
    (d) =>
      !d.message.startsWith("unsolved goals") &&
      (d.severity == DiagnosticSeverity.Error ) // || d.severity == DiagnosticSeverity.Warning
  )
}

// TODO: Didn't manage to unify this with the one above
export function hasInteractiveErrors (diags: InteractiveDiagnostic[]) {
  return (typeof diags !== 'undefined') && diags.some(
    (d) => (d.severity == DiagnosticSeverity.Error ) // || d.severity == DiagnosticSeverity.Warning
  )
}

export function getInteractiveDiagsAt (proof: ProofState, k : number) {
  if (k == 0) {
    return []
  } else if (k >= proof?.steps.length-1) {
    // TODO: Do we need that?
    return proof?.diagnostics.filter(msg => msg.range.start.line >= proof?.steps.length-1)
  } else {
    return proof?.diagnostics.filter(msg => msg.range.start.line == k-1)
  }
}
