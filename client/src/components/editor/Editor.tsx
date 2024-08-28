import * as React from 'react';
import Split from 'react-split'
import { useContext, useEffect, useRef, useState } from 'react'
import { useTranslation } from "react-i18next"
import { GameIdContext } from '../../state/context';
import { useLoadLevelQuery } from '../../state/api';
import { Markdown } from '../utils';
import * as monaco from 'monaco-editor'
import { LeanMonaco, LeanMonacoEditor, LeanMonacoOptions } from 'lean4monaco'

import '../../css/editor.css'
import { useSelector } from 'react-redux';
import { selectTypewriterMode } from '../../state/progress';

export function Editor() {
  let { t } = useTranslation()
  const {gameId, worldId, levelId } = useContext(GameIdContext)

  const typewriterMode = useSelector(selectTypewriterMode(gameId))

  const editorRef = useRef<HTMLDivElement>(null)
  const infoviewRef = useRef<HTMLDivElement>(null)
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
      websocket: {url: socketUrl},
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
        await leanMonacoEditor.start(editorRef.current!, `${gameId}/${worldId}/Level_${levelId}.lean`, code)

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

  return <Split direction='vertical' minSize={200} sizes={[50, 50]}
        className={`editor-wrapper ${typewriterMode ? 'hidden' : ''}`} >
      <div ref={editorRef} id="editor" />
      <div ref={infoviewRef} id="infoview" />
    </Split>
}
