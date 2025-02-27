import * as React from 'react';
import Split from 'react-split'
import { useContext, useEffect, useRef, useState } from 'react'
import { useTranslation } from "react-i18next"
import { GameIdContext, MonacoEditorContext } from '../../state/context';
import { useLoadLevelQuery } from '../../state/api';
import { Markdown } from '../utils';
import * as monaco from 'monaco-editor'
import { LeanMonaco, LeanMonacoEditor, LeanMonacoOptions } from 'lean4monaco'

import '../../css/editor.css'
import { useSelector } from 'react-redux';
import { selectTypewriterMode } from '../../state/progress';
import { Typewriter } from './typewriter';
import { GoalTabs } from './goal_tabs';
import { GameInfoview } from './tmp';

export function Editor() {
  let { t } = useTranslation()
  const {gameId, worldId, levelId } = useContext(GameIdContext)

  const typewriterMode = useSelector(selectTypewriterMode(gameId))

  const editorRef = useRef<HTMLDivElement>(null)
  const infoviewRef = useRef<HTMLDivElement>(null)
  const gameInfoviewRef = useRef<HTMLDivElement>(null)
  const [editor, setEditor] = useState<monaco.editor.IStandaloneCodeEditor>()
  const [leanMonaco, setLeanMonaco] = useState<LeanMonaco>()
  const [code, setCode] = useState<string>('')

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

        setEditor(leanMonacoEditor.editor)
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

  return <MonacoEditorContext.Provider value={editor}>
    <div className="editor-wrapper"><Split direction='vertical' minSize={200} sizes={[50, 50]}
          className={`editor-split ${typewriterMode ? 'hidden' : ''}`} >
        <div ref={editorRef} id="editor" />
        <div ref={infoviewRef} id="infoview" />
        {/* TODO: */}
        {/* <GameInfoview editorApi={null}/> */}
      </Split>
      {editor && typewriterMode && <Typewriter />}
    </div>
  </MonacoEditorContext.Provider>
}
