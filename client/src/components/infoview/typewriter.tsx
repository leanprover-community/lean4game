import * as React from 'react'
import { useRef, useState, useEffect } from 'react'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faWandMagicSparkles } from '@fortawesome/free-solid-svg-icons'
import * as monaco from 'monaco-editor/esm/vs/editor/editor.api.js'
import { Registry } from 'monaco-textmate' // peer dependency
import { wireTmGrammars } from 'monaco-editor-textmate'
import { DiagnosticSeverity, PublishDiagnosticsParams } from 'vscode-languageserver-protocol';
import { useServerNotificationEffect } from '../../../../node_modules/lean4-infoview/src/infoview/util';
import { AbbreviationRewriter } from 'lean4web/client/src/editor/abbreviation/rewriter/AbbreviationRewriter';
import { AbbreviationProvider } from 'lean4web/client/src/editor/abbreviation/AbbreviationProvider';
import * as leanSyntax from 'lean4web/client/src/syntaxes/lean.json'
import * as leanMarkdownSyntax from 'lean4web/client/src/syntaxes/lean-markdown.json'
import * as codeblockSyntax from 'lean4web/client/src/syntaxes/codeblock.json'
import languageConfig from 'lean4/language-configuration.json';
import { InteractiveDiagnostic, getInteractiveDiagnostics } from '@leanprover/infoview-api';
import { Diagnostic } from 'vscode-languageserver-types';
import { DocumentPosition } from '../../../../node_modules/lean4-infoview/src/infoview/util';
import { RpcContext } from '../../../../node_modules/lean4-infoview/src/infoview/rpcSessions';
import { DeletedChatContext, InputModeContext, MonacoEditorContext, ProofContext, ProofStep } from './context'
import { goalsToString } from './goals'
import { GameHint, InteractiveGoals } from './rpc_api'

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
export function Typewriter({hidden, disabled}: {hidden?: boolean, disabled?: boolean}) {

  /** Reference to the hidden multi-line editor */
  const editor = React.useContext(MonacoEditorContext)
  const model = editor.getModel()
  const uri = model.uri.toString()

  const [oneLineEditor, setOneLineEditor] = useState<monaco.editor.IStandaloneCodeEditor>(null)
  const [processing, setProcessing] = useState(false)

  const {typewriterInput, setTypewriterInput} = React.useContext(InputModeContext)

  const inputRef = useRef()

  // The context storing all information about the current proof
  const {proof, setProof} = React.useContext(ProofContext)

  // state to store the last batch of deleted messages
  const {setDeletedChat} = React.useContext(DeletedChatContext)

  const rpcSess = React.useContext(RpcContext)

  /** Load all goals an messages of the current proof (line-by-line) and save
   * the retrieved information into context (`ProofContext`)
   */
  const loadAllGoals = React.useCallback(() => {

    let goalCalls = []
    let msgCalls = []

    // For each line of code ask the server for the goals and the messages on this line
    for (let i = 0; i < model.getLineCount(); i++) {
      goalCalls.push(
        rpcSess.call('Game.getInteractiveGoals', DocumentPosition.toTdpp({line: i, character: 0, uri: uri}))
      )
      msgCalls.push(
        getInteractiveDiagnostics(rpcSess, {start: i, end: i+1}).catch((error) => {console.debug("promise broken")})
      )
    }

    // Wait for all these requests to be processed before saving the results
    Promise.all(goalCalls).then((steps : InteractiveGoals[]) => {
      Promise.all(msgCalls).then((diagnostics : [InteractiveDiagnostic[]]) => {
        let tmpProof : ProofStep[] = []

        let goalCount = 0

        steps.map((goals, i) => {
          // The first step has an empty command and therefore also no error messages
          // Usually there is a newline at the end of the editors content, so we need to
          // display diagnostics from potentally two lines in the last step.
          let messages = i ? (i == steps.length - 1 ? diagnostics.slice(i-1).flat() : diagnostics[i-1]) : []

          // Filter out the 'unsolved goals' message
          messages = messages.filter((msg) => {
            return !("append" in msg.message &&
              "text" in msg.message.append[0] &&
              msg.message.append[0].text === "unsolved goals")
          })

          if (typeof goals == 'undefined') {
            tmpProof.push({
              command: i ? model.getLineContent(i) : '',
              goals: [],
              hints: [],
              errors: messages
            } as ProofStep)
            console.debug('goals is undefined')
            return
          }

          // If the number of goals reduce, show a message
          if (goals.goals.length && goalCount > goals.goals.length) {
            messages.unshift({
              range: {
                start: {
                  line: i-1,
                  character: 0,
                },
                end: {
                  line: i-1,
                  character: 0,
                }},
              severity: DiagnosticSeverity.Information,
              message: {
              text: 'intermediate goal solved 🎉'
              }
            })
          }
          goalCount = goals.goals.length

          // with no goals there will be no hints.
          let hints : GameHint[] = goals.goals.length ? goals.goals[0].hints : []

          console.debug(`Command (${i}): `, i ? model.getLineContent(i) : '')
          console.debug(`Goals: (${i}): `, goalsToString(goals)) //
          console.debug(`Hints: (${i}): `, hints)
          console.debug(`Errors: (${i}): `, messages)

          tmpProof.push({
            // the command of the line above. Note that `getLineContent` starts counting
            // at `1` instead of `zero`. The first ProofStep will have an empty command.
            command: i ? model.getLineContent(i) : '',
            // TODO: store correct data
            goals: goals.goals,
            // only need the hints of the active goals in chat
            hints: hints,
            // errors and messages from the server
            errors: messages
          } as ProofStep)

        })
        // Save the proof to the context
        setProof(tmpProof)
      }).catch((error) => {console.debug("promise broken")})
    }).catch((error) => {console.debug("promise broken")})
  }, [editor, rpcSess, uri, model])

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
    }

    editor.setPosition(pos)
  }, [typewriterInput, editor])

  useEffect(() => {
    if (oneLineEditor && oneLineEditor.getValue() !== typewriterInput) {
      oneLineEditor.setValue(typewriterInput)
    }
  }, [typewriterInput])

  useEffect(() => {
    if (proof.length && hasInteractiveErrors(proof[proof.length - 1].errors)) {
      setTypewriterInput(proof[proof.length - 1].command)
    }
  }, [proof])

  // React when answer from the server comes back
  useServerNotificationEffect('textDocument/publishDiagnostics', (params: PublishDiagnosticsParams) => {
    if (params.uri == uri) {
      setProcessing(false)
      loadAllGoals()
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
    loadAllGoals()
  }, [rpcSess])

  /** Process the entered command */
  const handleSubmit : React.FormEventHandler<HTMLFormElement> = (ev) => {
    ev.preventDefault()
    runCommand()
  }

  return <div className={`typewriter${hidden ? ' hidden' : ''}${disabled ? ' disabled' : ''}`}>
      <form onSubmit={handleSubmit}>
        <div className="typewriter-input-wrapper">
          <div ref={inputRef} className="typewriter-input" />
        </div>
        <button type="submit" disabled={processing} className="btn btn-inverted">
          <FontAwesomeIcon icon={faWandMagicSparkles} /> Execute
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
