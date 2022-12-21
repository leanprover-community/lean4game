import * as React from 'react';
import { useEffect, useState, useRef } from 'react';
import { EditorApi } from '@leanprover/infoview-api'
import { LeanClient } from 'lean4web/client/src/editor/leanclient';
import * as monaco from 'monaco-editor/esm/vs/editor/editor.api.js'
import * as ls from 'vscode-languageserver-protocol'
import TacticState from './TacticState';

// TODO: move into Lean 4 web
function toLanguageServerPosition (pos: monaco.Position): ls.Position {
  return {line : pos.lineNumber - 1, character: pos.column - 1}
}

function Infoview({ editor, editorApi, leanClient } : {editor: monaco.editor.IStandaloneCodeEditor, editorApi: EditorApi, leanClient: LeanClient}) {
  const [rpcSession, setRpcSession] = useState<string>()
  const [goals, setGoals] = useState<any[]>(null)
  const [completed, setCompleted] = useState<boolean>(false)
  const [diagnostics, setDiagnostics] = useState<any[]>(undefined)

  /* `globalDiagnostics` is a work-around to show something when the proof is complete
  but had previous subgoals with `sorry` or errors.

  It is displayed whenever there are no goals and no (error)-messages present and the proof
  isn't complete. */
  const [globalDiagnostics, setGlobalDiagnostics] = useState<any[]>(undefined)

  const [uri, setUri] = useState<string>()

  const fetchInteractiveGoals = () => {
    if (editor && rpcSession) {
      const pos = toLanguageServerPosition(editor.getPosition())

      leanClient.sendRequest("$/lean/rpc/call", {"method":"Game.getGoals",
        "params":{"textDocument":{uri}, "position": pos},
        "sessionId":rpcSession,
        "textDocument":{uri},
        "position": pos
      }).then((res) => {
        setGoals(res ? res.goals : null)
        console.log(goals)
      }).catch((err) => {
        console.error(err)
      })

      leanClient.sendRequest("$/lean/rpc/call", {"method":"Game.getDiagnostics",
        "params":{"textDocument":{uri}, "lineRange": {start: pos.line, end: pos.line + 1}},
        "sessionId":rpcSession,
        "textDocument":{uri},
        "position": pos
      }).then((res) => {

        /* Workaround to not display the error `unsolved goals` */
        if (res) {res = res.filter(x => x.message.trim() !== 'unsolved goals')}

        setDiagnostics(res ? res : undefined)
        console.log(res)
      }).catch((err) => {
        console.error(err)
      })

    }
  }

  const checkCompleted = () => {
    if (editor && rpcSession) {
      const pos = toLanguageServerPosition(editor.getPosition())
      // Get all diagnostics independent of cursor position
      leanClient.sendRequest("$/lean/rpc/call", {"method":"Game.getDiagnostics",
        "params":{"textDocument":{uri},},
        "sessionId":rpcSession,
        "textDocument":{uri},
        "position": pos
      }).then((res) => {
        // Check that there are no errors and no warnings
        setCompleted(!res.some(({severity}) => severity <= 2))
        setGlobalDiagnostics(res)
      }).catch((err) => {
        console.error(err)
      })
    }
  }

  useEffect(() => {
    if (editor) {
      fetchInteractiveGoals()
      checkCompleted()
      const t = editor.onDidChangeModel((ev) => {
        if (ev.newModelUrl) {
          editorApi.closeRpcSession(rpcSession)
          setRpcSession(undefined)
          setUri(ev.newModelUrl.toString())
          editorApi.createRpcSession(ev.newModelUrl.toString()).then((rpcSession) => {
            setRpcSession(rpcSession)
          })
        }
      })
      return () => {t.dispose()}
    }
  }, [editor, rpcSession]);

  useEffect(() => {
    if (editor) {
      const t = editor.onDidChangeCursorPosition(async (ev) => {
        fetchInteractiveGoals()
      })
      return () => { t.dispose() }
    }
  }, [editor, rpcSession])

  useEffect(() => {
    const t = leanClient.didChange(async (ev) => {
      fetchInteractiveGoals()
      checkCompleted()
    })
    return () => { t.dispose() }
  }, [editor, leanClient, rpcSession])

  return (<div>
    <TacticState goals={goals} diagnostics={diagnostics} completed={completed}
      globalDiagnostics={globalDiagnostics}></TacticState>
  </div>)
}

export default Infoview