import * as React from 'react';
import { useEffect, useState, useRef } from 'react';
import { EditorApi } from '@leanprover/infoview-api'
import { LeanClient } from 'lean4web/client/src/editor/leanclient';
import * as monaco from 'monaco-editor/esm/vs/editor/editor.api.js'
import * as ls from 'vscode-languageserver-protocol'

// TODO: move into Lean 4 web
function toLanguageServerPosition (pos: monaco.Position): ls.Position {
  return {line : pos.lineNumber - 1, character: pos.column - 1}
}

function Infoview({ ready, editor, editorApi, uri, leanClient } : {ready: boolean, editor: monaco.editor.IStandaloneCodeEditor, editorApi: EditorApi, uri: any, leanClient: LeanClient}) {
  const [rpcSession, setRpcSession] = useState<string>()
  const [goals, setGoals] = useState<any[]>(null)
  const liftOff = async () => {
    const rpcSession = await editorApi.createRpcSession(uri)
    const fetchInteractiveGoals = () => {
      const pos = toLanguageServerPosition(editor.getPosition())
      leanClient.sendRequest("$/lean/rpc/call", {"method":"Lean.Widget.getInteractiveGoals",
        "params":{"textDocument":{uri}, "position": pos},
        "sessionId":rpcSession,
        "textDocument":{uri},
        "position": pos
      }).then(({ goals }) => {
        setGoals(goals)
      }).catch((err) => {
        console.error(err)
      })
    }
    setRpcSession(rpcSession)
    editor.onDidChangeCursorPosition((ev) => {
      fetchInteractiveGoals()
    })
    leanClient.didChange(async (ev) => {
      fetchInteractiveGoals()
    })
  }

  useEffect(() => {
    if (ready) {
      liftOff()
    }
  }, [ready])
   // Lean.Widget.getInteractiveGoals

  return (<div>Number of Goals: {goals !== null ? goals.length : "None"}</div>)
}

export default Infoview
