import * as React from 'react'
import { useRef, useState, useEffect, useContext } from 'react'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faWandMagicSparkles } from '@fortawesome/free-solid-svg-icons'
import * as monaco from 'monaco-editor/esm/vs/editor/editor.api.js'
import { DiagnosticSeverity, PublishDiagnosticsParams, DocumentUri } from 'vscode-languageserver-protocol';
import { useServerNotificationEffect } from '../../../../node_modules/vscode-lean4/lean4-infoview/src/infoview/util';
import { InteractiveDiagnostic, RpcSessionAtPos, getInteractiveDiagnostics } from '@leanprover/infoview-api';
import { Diagnostic } from 'vscode-languageserver-types';
import { DocumentPosition } from '../../../../node_modules/vscode-lean4/lean4-infoview/src/infoview/util';
import { RpcContext } from '../../../../node_modules/vscode-lean4/lean4-infoview/src/infoview/rpcSessions';
import { DeletedChatContext, MonacoEditorContext, ProofContext } from './context'
import { goalsToString, lastStepHasErrors, loadGoals } from './goals'
import { GameHint, ProofState } from './rpc_api'
import { useTranslation } from 'react-i18next'
import { useAtom } from 'jotai'
import { levelIdAtom, worldIdAtom } from '../../store/location-atoms'
import { preferencesAtom } from '../../store/preferences-atoms'
import { typewriterContentAtom } from '../../store/editor-atoms'

export interface GameDiagnosticsParams {
  uri: DocumentUri;
  diagnostics: Diagnostic[];
}

/** The input field */
export function Typewriter({disabled}: {disabled?: boolean}) {
  let { t } = useTranslation()

  /** Reference to the hidden multi-line editor */
  const editor = React.useContext(MonacoEditorContext)
  const model = editor?.getModel()
  const uri = model?.uri.toString() ?? ''
  const hasEditor = Boolean(editor && model)

  const [worldId] = useAtom(worldIdAtom)
  const [levelId] = useAtom(levelIdAtom)

  const [oneLineEditor, setOneLineEditor] = useState<monaco.editor.IStandaloneCodeEditor>()
  const oneLineEditorRef = useRef<monaco.editor.IStandaloneCodeEditor>(null)
  const [processing, setProcessing] = useState(false)

  const [typewriter, setTypewriter] = useAtom(typewriterContentAtom)

  const inputRef = useRef<HTMLDivElement>()

  // The context storing all information about the current proof
  const {proof, setProof, interimDiags, setInterimDiags, setCrashed} = React.useContext(ProofContext)

  // state to store the last batch of deleted messages
  const {setDeletedChat} = React.useContext(DeletedChatContext)

  const rpcSess = React.useContext(RpcContext)

  // Run the command
  const runCommand = React.useCallback(() => {
    if (processing || !hasEditor) {return}

    // TODO: Desired logic is to only reset this after a new *error-free* command has been entered
    setDeletedChat([])

    const pos = editor.getPosition()
    if (typewriter) {
      setProcessing(true)
      editor.executeEdits("typewriter", [{
        range: monaco.Selection.fromPositions(
          pos,
          editor.getModel()?.getFullModelRange().getEndPosition()
        ),
        text: typewriter.trim() + "\n",
        forceMoveMarkers: false
      }])
      setTypewriter('')
      // Load proof after executing edits
      loadGoals(rpcSess, uri, worldId!, levelId!, setProof, setCrashed)
    }

    editor.setPosition(pos)
  }, [typewriter, editor])

  const [{ isSuggestionsMobileMode }] = useAtom(preferencesAtom)

  useEffect(() => {
    if (oneLineEditor && oneLineEditor.getValue() !== typewriter) {
      oneLineEditor.setValue(typewriter)
      oneLineEditor.setPosition({ column: typewriter.length + 1, lineNumber: 1 })
      isSuggestionsMobileMode || oneLineEditor.focus()
    }
  }, [typewriter])

  useEffect(() => {
    if (oneLineEditor && hasEditor) {
      oneLineEditor.setPosition({ column: editor.getValue().length + 1, lineNumber: 1 })
      isSuggestionsMobileMode || oneLineEditor.focus()
    }
  }, [oneLineEditor, hasEditor, isSuggestionsMobileMode, editor])

  /** If the last step has an error, add the command to the typewriter. */
  useEffect(() => {
    if (lastStepHasErrors(proof)) {
      setTypewriter(proof?.steps[proof?.steps.length - 1].command)
    }
  }, [proof])

  // React when answer from the server comes back
  useServerNotificationEffect('textDocument/publishDiagnostics', (params: PublishDiagnosticsParams) => {
    if (!hasEditor) {
      return
    }
    if (params.uri == uri) {
      setProcessing(false)

      const seriousDiags = params.diagnostics.filter(diag =>
        diag.severity === DiagnosticSeverity.Error || diag.severity === DiagnosticSeverity.Warning
      )
      setInterimDiags(seriousDiags)
      // loadGoals(rpcSess, uri, worldId, levelId, setProof, setCrashed)

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
  }, [uri, hasEditor, editor]);

  // // React when answer from the server comes back
  // useServerNotificationEffect('$/game/publishDiagnostics', (params: GameDiagnosticsParams) => {
  //   console.log('Received game diagnostics')
  //   console.log(`diag. uri : ${params.uri}`)
  //   console.log(params.diagnostics)

  // }, [uri]);


  useEffect(() => {
    if (oneLineEditorRef.current) {
      return
    }
    const myEditor = monaco.editor.create(inputRef.current!, {
      value: typewriter,
      language: "lean4",
      quickSuggestions: false,
      // lightbulb: {
      //   enabled: true
      // },
      unicodeHighlight: {
          ambiguousCharacters: false,
      },
      automaticLayout: true,
      minimap: {
        enabled: false
      },
      lineNumbers: 'off',
      tabSize: 2,
      wordWrap: 'on',
      glyphMargin: false,
      folding: false,
      lineDecorationsWidth: 0,
      lineNumbersMinChars: 0,
      'semanticHighlighting.enabled': true,
      overviewRulerLanes: 0,
      hideCursorInOverviewRuler: true,
      padding: {
        top: 0,
        bottom: 0,
      },
      scrollbar: {
        verticalScrollbarSize: 3
      },
      scrollBeyondLastLine: false,
      overviewRulerBorder: false,
      theme: 'vs-code-theme-converted',
      contextmenu: false
    })

    const layoutInput = () => {
      const lineHeight = myEditor.getOption(monaco.editor.EditorOption.lineHeight)
      const height = Math.min(myEditor.getContentHeight(), lineHeight + 2, window.innerHeight / 3)
      inputRef.current.style.height = `${height}px`
      myEditor.layout({
        width: inputRef.current.clientWidth,
        height
      })
    }
    myEditor.onDidContentSizeChange(layoutInput)
    layoutInput()

    oneLineEditorRef.current = myEditor
    setOneLineEditor(myEditor)

    // const abbrevRewriter = new AbbreviationRewriter(new AbbreviationProvider(), myEditor.getModel(), myEditor)

    return () => {
      // abbrevRewriter.dispose()
      myEditor.dispose()
      oneLineEditorRef.current = null
      setOneLineEditor(undefined)
    }
  }, [])

  useEffect(() => {
    if (!oneLineEditor) return
    // Ensure that our one-line editor can only have a single line
    const l = oneLineEditor.getModel()?.onDidChangeContent((e) => {
      const value = oneLineEditor.getValue()
      setTypewriter(value)
      const newValue = value.replace(/[\n\r]/g, '')
      if (value != newValue) {
        oneLineEditor.setValue(newValue)
      }
    })
    return () => {
      if (typeof (l as any)?.dispose === 'function') {
        l.dispose()
      } else if (typeof l === 'function') {
        l()
      }
    }
  }, [oneLineEditor, setTypewriter])

  useEffect(() => {
    if (!oneLineEditor) return
    // Run command when pressing enter (and block newline insertion)
    const l = oneLineEditor.onKeyDown((ev) => {
      if (ev.code === "Enter" || ev.code === "NumpadEnter") {
        ev.preventDefault()
        runCommand()
      }
    })
    return () => {
      if (typeof (l as any)?.dispose === 'function') {
        l.dispose()
      } else if (typeof l === 'function') {
        l()
      }
    }
  }, [oneLineEditor, runCommand])

  // // BUG: Causes `file closed` error
  // //TODO: Intention is to run once when loading, does that work?
  // useEffect(() => {
  //   console.debug(`time to update: ${uri} \n ${rpcSess}`)
  //   console.debug(rpcSess)
  //   // console.debug('LOAD ALL GOALS')
  //   // TODO: loadAllGoals()
  // }, [rpcSess])

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
