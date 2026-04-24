import React, { useEffect, useRef } from "react";

import "../../../css/typewriter.css"
import { useTranslation } from "react-i18next";
import { FontAwesomeIcon } from "@fortawesome/react-fontawesome";
import { faWandMagicSparkles } from "@fortawesome/free-solid-svg-icons";
import { useAtom, useSetAtom } from "jotai";

import * as monaco from 'monaco-editor'
import { typewriterContentAtom, restoreErrorCommandEffect, oneLineEditorAtom, syncTypewriterToEditorEffect, syncEditorPositionEffect, isProcessingAtom, runCommandAtom } from "../../../store/editor-atoms";
import { proofAtom } from "../../../store/editor-atoms";

/** The input field */
export function TypewriterCommandLine() {
  let { t } = useTranslation()

  const [typewriter, setTypewriter] = useAtom(typewriterContentAtom)
  const [oneLineEditor, setOneLineEditor] = useAtom(oneLineEditorAtom)
  const [proof] = useAtom(proofAtom)
  const [isProcessing] = useAtom(isProcessingAtom)
  const runCommand = useSetAtom(runCommandAtom)

  // useAtom(syncTypewriterToEditorEffect)
  // useAtom(syncEditorPositionEffect)
  // useAtom(restoreErrorCommandEffect)

  const oneLineEditorRef = useRef<monaco.editor.IStandaloneCodeEditor | null>(null)
  const inputRef = useRef<HTMLDivElement>(null)

  useEffect(() => {
    console.log("TypewriterCommandLine: Editor initialization useEffect")

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
        console.log(`Single-line editor width: ${inputRef.current.clientWidth}`)
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
      console.log(`Editor content changed to: "${value}"`)
      setTypewriter(value)

      // Prevent newlines (single-line behavior)
      const newValue = value.replace(/[\n\r]/g, '')
      if (value !== newValue) {
        myEditor.setValue(newValue)
      }
    })

    const keyDownDisposable = myEditor.onKeyDown((ev) => {
      if (ev.code === "Enter" || ev.code === "NumpadEnter") {
        ev.preventDefault()
        console.log("Enter pressed, running command...")
        runCommand()
      }
    })

    oneLineEditorRef.current = myEditor
    setOneLineEditor(myEditor)
    console.log("Editor initialized successfully")

    return () => {
      console.log("Cleaning up editor...")
      changeDisposable?.dispose()
      keyDownDisposable?.dispose()
      myEditor.dispose()
      oneLineEditorRef.current = null
      setOneLineEditor(null)
    }
  }, [setTypewriter, setOneLineEditor, runCommand])

  //const oneLineEditorRef = useRef<any>(null)
  //const [typewriterContent, setTypewriterContent] = useState("")
  //const leanMonacoEditor = useAtom(leanMonacoEditorAtom)
  //let inputRef = getInputRef()

  /** Process the entered command */
  const handleSubmit : React.FormEventHandler<HTMLFormElement> = (ev) => {
    ev.preventDefault()
    console.debug("execute!")
    runCommand()
  }

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
