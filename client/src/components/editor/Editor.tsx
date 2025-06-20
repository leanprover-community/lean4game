import * as React from 'react';
import Split from 'react-split'
import { useContext, useEffect, useRef, useState } from 'react'
import { useTranslation } from "react-i18next"
import { GameIdContext, MonacoEditorContext } from '../../state/context';
import { useLoadLevelQuery } from '../../state/api';
import { Markdown } from '../utils';
import * as monaco from 'monaco-editor'
import { LeanMonaco, LeanMonacoEditor, LeanMonacoOptions } from 'lean4monaco'
import {RpcConnected, RpcConnectParams} from '@leanprover/infoview-api'
import '../../css/editor.css'
import { useSelector } from 'react-redux';
import { selectTypewriterMode } from '../../state/progress';
import { Typewriter } from './Typewriter';
import { GoalTabs } from './goal_tabs';
import { GameInfoview } from './tmp';
import { LeanClient } from 'lean4monaco/dist/vscode-lean4/vscode-lean4/src/leanclient'
// import { parseExtUri } from 'lean4monaco/dist/vscode-lean4/vscode-lean4/src/utils/exturi';

// import { LeanMonacoContext } from './LeanMonaco'
import { RpcSessionAtPos } from 'lean4monaco/dist/vscode-lean4/vscode-lean4/src/infoview'
import { Uri } from 'monaco-editor';

export function Editor() {
  let { t } = useTranslation()
  const {gameId, worldId, levelId } = useContext(GameIdContext)

  const typewriterMode = useSelector(selectTypewriterMode(gameId))

  const editorRef = useRef<HTMLDivElement>(null)
  const infoviewRef = useRef<HTMLDivElement>(null)
  const gameInfoviewRef = useRef<HTMLDivElement>(null)
  const [leanMonacoEditor, setLeanMonacoEditor] = useState<LeanMonacoEditor>(undefined)
  const [leanMonaco, setLeanMonaco] = useState<LeanMonaco>()
  const [code, setCode] = useState<string>('')

  const [client, setClient] = useState<LeanClient | null>(null)
  const [uri, setUri] = useState<Uri | null>(null)
  const [rpcSess, setRpcSess] = useState<RpcSessionAtPos|null>(null)

  const [options, setOptions] = useState<LeanMonacoOptions>({
    // placeholder. gets set below
    websocket: {
      url: ''
    }
  })

  // Update LeanMonaco options when preferences are loaded or change
  useEffect(() => {
    var socketUrl = ((window.location.protocol === "https:") ? "wss://" : "ws://") +
      window.location.host + `/websocket/${gameId}`
    console.log(`[LeanGame] socket url: ${socketUrl}`)
    var _options: LeanMonacoOptions = {
      websocket: {
        url: socketUrl,
        // @ts-ignore
        difficulty: 1,
        inventory: []
      },
      // Restrict monaco's extend (e.g. context menu) to the editor itself
      htmlElement: editorRef.current ?? undefined,
      vscode: {
        /* To add settings here, you can open your settings in VSCode (Ctrl+,), search
         * for the desired setting, select "Copy Setting as JSON" from the "More Actions"
         * menu next to the selected setting, and paste the copied string here.
         */
        // "workbench.colorTheme": preferences.theme,
        "editor.tabSize": 2,
        // "editor.rulers": [100],
        "editor.lightbulb.enabled": "on",
        "editor.wordWrap": "on",
        "editor.wrappingStrategy": "advanced",
        "editor.semanticHighlighting.enabled": true,
        "editor.acceptSuggestionOnEnter": "off",
        "lean4.input.eagerReplacementEnabled": true,
        // "lean4.input.leader": preferences.abbreviationCharacter
      }
    }
    setOptions(_options)
  }, [editorRef])

  // Setting up the editor and infoview
  useEffect(() => {
    console.debug('[LeanGame] Restarting Editor!')
    var _leanMonaco = new LeanMonaco()

    var leanMonacoEditor = new LeanMonacoEditor()

    _leanMonaco.setInfoviewElement(infoviewRef.current!)
    ;(async () => {
        await _leanMonaco.start(options)

        // JE: how do I get the editorApi or an RPC session?
        // let infoProvider = _leanMonaco.infoProvider.editorApi

        console.warn('gameId', gameId)
        await leanMonacoEditor.start(editorRef.current!, `/${worldId}/L_${levelId}.lean`, code)

        setLeanMonacoEditor(leanMonacoEditor)
        setLeanMonaco(_leanMonaco)

        // Keeping the `code` state up-to-date with the changes in the editor
        leanMonacoEditor.editor?.onDidChangeModelContent(() => {
          setCode(leanMonacoEditor.editor?.getModel()?.getValue()!)
        })
    })()
    return () => {
      leanMonacoEditor.dispose()
      _leanMonaco.dispose()
    }
  }, [options, infoviewRef, editorRef, gameId, worldId, levelId])

// RPC session: start new rpc session using `uri` and `client`
useEffect(() => {
  console.log('connecting to RPC')

  if (!(leanMonacoEditor?.editor) || !(leanMonaco?.clientProvider)) { return }

  const updateUri = () => {
    const model = leanMonacoEditor.editor.getModel()
    if (model?.uri) {
      setUri(model.uri)
      return true
    }
    return false
  }
  const updateClient = () => {
    const clients = leanMonaco.clientProvider.getClients()
    if (clients?.[0]?.running) {
      setClient(clients[0])
      return true
    }
    return false
  }
  const tryUpdate = () => {
    const uriUpdated = updateUri()
    const clientUpdated = updateClient()
    if (uriUpdated && clientUpdated) {
      console.log('updated client and uri')
      clearInterval(interval)
    }
  }
  tryUpdate()
  const interval = setInterval(tryUpdate, 500)
  return () => clearInterval(interval)
}, [leanMonaco?.clientProvider, leanMonacoEditor?.editor])

// RPC session: wait until the `uri` is defined
useEffect(() => {
  if (!client || !uri) { return }
  console.log('connecting to RPC')
  console.log(`client: ${client}`)
  console.log(client)
  console.log(`uri: ${uri}`)

  client.sendRequest('$/lean/rpc/connect', {uri: uri.toString()} as RpcConnectParams).then(result => {
    const sessionId = result.sessionId
    console.debug(`session id: ${sessionId}`)
    let _rpcSess = new RpcSessionAtPos(client, sessionId, uri.toString())
    setRpcSess(_rpcSess)
  }).catch(
    reason => {console.error(`failed: ${reason}`)}
  )

  return () => {
    rpcSess?.dispose()
  }
}, [client, uri])

  return <MonacoEditorContext.Provider value={{leanMonacoEditor, leanMonaco, rpcSess}}>
    <div className="editor-wrapper"><Split direction='vertical' minSize={200} sizes={[50, 50]}
          className={`editor-split ${typewriterMode ? 'hidden' : ''}`} >
        <div ref={editorRef} id="editor" />
        <div ref={infoviewRef} id="infoview" />
        {/* TODO: */}
        {/* <GameInfoview editorApi={null}/> */}
      </Split>
      {leanMonacoEditor && typewriterMode && <Typewriter />}
    </div>
  </MonacoEditorContext.Provider>
}
