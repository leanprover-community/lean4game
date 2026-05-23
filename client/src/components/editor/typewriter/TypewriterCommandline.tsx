import React, { FormEvent, useEffect, useRef, useState } from "react";
import "../../../css/typewriter.css"
import { useTranslation } from "react-i18next";
import { FontAwesomeIcon } from "@fortawesome/react-fontawesome";
import { faWandMagicSparkles } from "@fortawesome/free-solid-svg-icons";
import { useAtom } from "jotai";
import * as monaco from 'monaco-editor'
import { typewriterContentAtom, codeAtom, modelAtom } from "../../../store/editor-atoms";
import { twMerge } from "tailwind-merge";
import { deletedChatAtom } from "../../../store/chat-atoms";
import { oneLineEditorAtom } from "./typewriter-atoms";

/** The input field */
export function TypewriterCommandLine() {
  let { t } = useTranslation()
  const [isProcessing, setProcessing] = useState(false)
  const [oneLineEditor, setOneLineEditor] = useAtom(oneLineEditorAtom)
  const [model] = useAtom(modelAtom)
  const [code] = useAtom(codeAtom)
  const [, setDeletedChatAtom] = useAtom(deletedChatAtom)
  const [typewriter, setTypewriter] = useAtom(typewriterContentAtom)
  const oneLineEditorRef = useRef<monaco.editor.IStandaloneCodeEditor | null>(null)
  const inputRef = useRef<HTMLDivElement>(null)

  /** Handle keyboard events */
  function handleKeyDown(event: KeyboardEvent) {
    if (event.key == "Enter" || event.key == "NumpadEnter") {
      event.preventDefault()
      handleSubmit()
    }
  }

  /** Wrapper to set the typewriter to processing. */
  function handleSubmit(ev?: FormEvent<HTMLFormElement>) {
    ev?.preventDefault()
    setProcessing(true)
    try { handleSubmitAux(ev) } finally { setProcessing(false) }
  }

  /** Process the entered command */
  async function handleSubmitAux(ev?: FormEvent<HTMLFormElement>) {
    const content = typewriter.trimEnd()
    if (content.length == 0) return

    // Add typewriter content to the editor


    // TODO: Desired logic is to only reset this after a new *error-free* command has been entered
    setDeletedChatAtom([])

    // Clear typewriter
    oneLineEditor?.getModel()?.setValue('')
  }

  // start the editor used in the typewriter command line
  useEffect(() => {
    // Guard: only create once
    if (oneLineEditorRef.current) {
      console.log("Editor already exists, skipping initialization")
      return
    }

    // Guard: wait for DOM element
    if (!inputRef.current) {
      console.log("inputRef.current is not ready yet")
      return
    }

    const editorConfig: monaco.editor.IStandaloneEditorConstructionOptions = {
      value: typewriter,
      language: "lean4",
      quickSuggestions: false,
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
    }

    console.log("Creating Monaco editor instance...")
    const myEditor = monaco.editor.create(inputRef.current, editorConfig)

    const layoutInput = () => {
      const lineHeight = myEditor.getOption(monaco.editor.EditorOption.lineHeight)
      const height = Math.min(myEditor.getContentHeight(), lineHeight + 2, window.innerHeight / 3)
      if (inputRef.current) {
        inputRef.current.style.height = `${height}px`
        myEditor.layout({
          width: inputRef.current.clientWidth,
          height
        })
      }
    }

    myEditor.onDidContentSizeChange(layoutInput)
    layoutInput()

    const changeDisposable = myEditor.getModel()?.onDidChangeContent(() => {
      const value = myEditor.getValue()
      setTypewriter(value)

      // Prevent newlines (single-line behavior)
      const newValue = value.replace(/[\n\r]/g, '')
      if (value !== newValue) {
        myEditor.setValue(newValue)
      }
    })

    oneLineEditorRef.current = myEditor
    setOneLineEditor(myEditor)
    console.log("Editor initialized successfully")

    return () => {
      console.log("Cleaning up editor...")
      changeDisposable?.dispose()
      myEditor.dispose()
      oneLineEditorRef.current = null
      setOneLineEditor(null)
    }
  }, [setTypewriter, setOneLineEditor])

  // Handle keyboard events (i.e. "Enter")
  useEffect(() => {
    document.addEventListener('keydown', handleKeyDown)
    return () => {
      document.removeEventListener('keydown', handleKeyDown)
    }
  }, [handleKeyDown])

  // do not display if the proof is completed (with potential warnings still present)
  return <div className={twMerge("typewriter", isProcessing && "disabled")}>
        <form onSubmit={handleSubmit}>
          <div className="typewriter-input-wrapper">
            <div ref={inputRef} className="typewriter-input" />
          </div>
          <button type="submit" disabled={isProcessing} className="btn btn-inverted">
            <FontAwesomeIcon icon={faWandMagicSparkles} />&nbsp;{t("Execute")}
          </button>
        </form>
      </div>
}
