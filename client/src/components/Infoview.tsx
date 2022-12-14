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
  const [errors, setErrors] = useState<any[]>(undefined)
  const [uri, setUri] = useState<string>()
  console.log(rpcSession)
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
        "params":{"textDocument":{uri}, "position": pos},
        "sessionId":rpcSession,
        "textDocument":{uri},
        "position": pos
      }).then((res) => {
        setErrors(res ? res : undefined)
        console.log(res)
      }).catch((err) => {
        console.error(err)
      })

    }
  }

  useEffect(() => {
    if (editor) {
      fetchInteractiveGoals()
      const t = editor.onDidChangeModel((ev) => {
        if (ev.newModelUrl) {
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
    })
    return () => { t.dispose() }
  }, [editor, leanClient, rpcSession])

  return (<div>
    <TacticState goals={goals} errors={errors} completed={goals?.length === 0 && errors?.length === 0}></TacticState>
  </div>)
}

export default Infoview
