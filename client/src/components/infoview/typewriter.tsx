import React, { MutableRefObject, useEffect, useRef, useState } from "react";

import "../../css/typewriter.css"
import { useTranslation } from "react-i18next";
import { FontAwesomeIcon } from "@fortawesome/react-fontawesome";
import { faWandMagicSparkles } from "@fortawesome/free-solid-svg-icons";
import { useAtom } from "jotai";
import { gameInfoAtom } from "../../store/query-atoms";

import { DiagnosticSeverity, PublishDiagnosticsParams, DocumentUri } from 'vscode-languageserver-protocol';
import * as monaco from 'monaco-editor'
import { levelIdAtom, gameIdAtom, worldIdAtom } from "../../store/location-atoms";
import { leanMonacoEditorAtom, typewriterContentAtom, interimDiagsAtom, crashedAtom, leanMonacoEditorModelAtom, leanMonacoEditorUriAtom, hasLeanMonacoEditorAtom, lastProofStepErrorCommandAtom, restoreErrorCommandEffect, oneLineEditorAtom, syncTypewriterToEditorEffect, syncEditorPositionEffect } from "../../store/editor-atoms";
import { deletedChatAtom } from '../../store/chat-atoms'
import { preferencesAtom } from '../../store/preferences-atoms'

import path from "node:path";
import { proofAtom } from "../../store/editor-atoms";
import { ExerciseStatement } from "./ExerciseStatement";
import { ProofStep } from "./ProofStep";

/**
 * Der Typewriter bestehend aus Eingabezeile, Beweisschritten, Aufgabenstellung und Hintergrundbild
 */
export function Typewriter() {
  const [{ data: gameInfo }] = useAtom(gameInfoAtom)
  const [gameId, navigateToGame] = useAtom(gameIdAtom)
  const [worldId] = useAtom(worldIdAtom)
  const [proof, setProof ] = useAtom(proofAtom)

  const proofPanelRef = useRef<HTMLDivElement>(null)

  let image = gameInfo?.worlds?.nodes[worldId!]?.image

  return <div className="typewriter-canvas">
    <div className="typewriter-info">
      {image && <img className="world-image contain" src={path.join("data", gameId!, image)} alt="" />}
      <div className="pusher" />
      <div className='proof' ref={proofPanelRef}>
        <ExerciseStatement showLeanStatement={true} />
        {proof?.steps.map((step, i) => <ProofStep step={step} idx={i} />)}
      </div>
    </div>
    <TypewriterCommandLine />
  </div>
}

/** The input field */
export function TypewriterCommandLine() {
  let { t } = useTranslation()
  const oneLineEditorRef = useRef<any>(null)
  const [typewriterContent, setTypewriterContent] = useState("")

  /** Process the entered command */
  const handleSubmit : React.FormEventHandler<HTMLFormElement> = (ev) => {
    ev.preventDefault()
    // runCommand()
  }

  let inputRef = getInputRef()

  // do not display if the proof is completed (with potential warnings still present)
  return <div className="typewriter">
      <form onSubmit={handleSubmit}>
        <div className="typewriter-input-wrapper">
          <div ref={inputRef} className="typewriter-input" />
        </div>
        <button type="submit" disabled={false /* TODO */} className="btn btn-inverted">
          <FontAwesomeIcon icon={faWandMagicSparkles} />&nbsp;{t("Execute")}
        </button>
      </form>
    </div>
}

export function getInputRef() {
  const [typewriter, setTypewriter] = useAtom(typewriterContentAtom)
  const [oneLineEditor, setOneLineEditor] = useAtom(oneLineEditorAtom)
  // added mutability so oneLineEditorRef.current can be reassigned
  const oneLineEditorRef = useRef<monaco.editor.IStandaloneCodeEditor>(null) as MutableRefObject<monaco.editor.IStandaloneCodeEditor | null>
  const inputRef = useRef<HTMLDivElement>()

  useAtom(syncTypewriterToEditorEffect)
  useAtom(syncEditorPositionEffect)

  useEffect(() => {
    console.log("getInputRef useEffect")
    if (oneLineEditorRef.current) {
      console.log("oneLineEditorRef.current is")
      return
    }

    const editorConfig: monaco.editor.IStandaloneEditorConstructionOptions = {
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
    };

    const myEditor = monaco.editor.create(inputRef.current!, editorConfig)

    const layoutInput = () => {
      const lineHeight = myEditor.getOption(monaco.editor.EditorOption.lineHeight)
      const height = Math.min(myEditor.getContentHeight(), lineHeight + 2, window.innerHeight / 3)
      inputRef.current!.style.height = `${height}px`
      console.log(`width of single line editor: ${inputRef.current!.clientWidth}`)
      myEditor.layout({
        width: inputRef.current!.clientWidth,
        height
      })
    }

    myEditor.onDidContentSizeChange(layoutInput)
    layoutInput()

    oneLineEditorRef.current = myEditor
    setOneLineEditor(myEditor)

    return () => {
      // abbrevRewriter.dispose()
      myEditor.dispose()
      oneLineEditorRef.current = null
      setOneLineEditor(null)
    }
  }, [])

  return inputRef
}
