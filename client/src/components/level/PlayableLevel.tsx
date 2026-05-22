import { useTranslation } from "react-i18next"
import { useGameTranslation } from "../../utils/translation"
import { useEffect, useRef, useState } from "react"
import { useAtom } from "jotai"
import { clientAtom, codeStorageAtom, rpcSessionAtom, editorAtom, leanMonacoAtom, lockEditorModeAtom, modelAtom, typewriterModeAtom, uriAtom } from "../../store/editor-atoms"
import { gameIdAtom, levelIdAtom, worldIdAtom } from "../../store/location-atoms"
import { mobileAtom } from "../../store/preferences-atoms"
import { gameInfoAtom, levelInfoAtom } from "../../store/query-atoms"
import { LeanMonacoEditor, RpcSessionAtPos } from "lean4monaco"
import { RpcConnectParams } from "@leanprover/infoview-api"
import { CircularProgress } from "@mui/material"
import { LevelAppBar } from "../app_bar"
import React from "react"
import { ExercisePanel } from "./ExercisePanel"
import { InventoryPanel } from "../inventory/inventory_panel"
import { ChatPanel } from "../chat/ChatPanel"
import Split from 'react-split'

export function PlayableLevel() {
  let { t } = useTranslation()
  const { t : gT } = useGameTranslation()
  const codeviewRef = useRef<HTMLDivElement>(null)
  const [leanMonaco] = useAtom(leanMonacoAtom)
  const [gameId] = useAtom(gameIdAtom)
  const [worldId] = useAtom(worldIdAtom)
  const [levelId] = useAtom(levelIdAtom)
  const [typewriterMode, setTypewriterMode] = useAtom(typewriterModeAtom)
  const [mobile] = useAtom(mobileAtom)
  const [code, setCode] = useAtom(codeStorageAtom)
  const [{ data: gameInfo }] = useAtom(gameInfoAtom)
  const [{ data: levelInfo, isLoading: levelInfoIsLoading }] = useAtom(levelInfoAtom)
  // Only for mobile layout
  const [pageNumber, setPageNumber] = useState(0)
  // set to true to prevent switching between typewriter and editor
  const [lockEditorMode] = useAtom(lockEditorModeAtom)
  const [, setTypewriterInput] = useState("")
  const lastLevel = worldId && (levelId !== undefined) && levelId >= (gameInfo?.worldSize?.[worldId] ?? 0)

  // When clicking on an inventory item, the inventory is overlayed by the item's doc.
  // If this state is set to a pair `(name, type)` then the according doc will be open.
  // Set `inventoryDoc` to `null` to close the doc
  const [inventoryDoc, setInventoryDoc] = useState<{name: string, type: string} | null>(null)
  function closeInventoryDoc () {setInventoryDoc(null)}

  const [editor, setEditor] = useAtom(editorAtom)
  const [model] = useAtom(modelAtom)
  const [client, setClient] = useAtom(clientAtom)
  const [uri] = useAtom(uriAtom)
  const [rpcSess, setRpcSess] = useAtom(rpcSessionAtom)

  // Start the editor, following lean4monaco demo
  useEffect(() => {
    if (leanMonaco) {
      const leanMonacoEditor = new LeanMonacoEditor()
      const uriStr = `file:///${worldId}/${levelId}.lean`

      ;(async () => {
        await leanMonaco!.whenReady
        console.debug('[lean4game]: starting editor')
        await leanMonacoEditor.start(codeviewRef.current!, uriStr, code ?? "")
        console.debug('[lean4game]: editor started')
        setEditor(leanMonacoEditor.editor)
      })()

      return () => {
        leanMonacoEditor.dispose()
      }
    }
  }, [leanMonaco, worldId, levelId])

  // Persist editor text into progress whenever the model changes.
  useEffect(() => {
    if (!editor) return

    setCode(editor.getValue())
    const disposable = editor.onDidChangeModelContent(() => {
      setCode(editor.getValue())
    })

    return () => {
      disposable.dispose()
    }
  }, [editor, setCode])

  // wait until the client exists
  // TODO: it didn't work to define an atom `get(editorAtom)?.clientProvider?.getClients()?.[0]`
  // is there a way to tell atoms to fully reevaluate until they get a non-null result?
  useEffect(() => {
    const updateClient = () => {
      const clients = leanMonaco?.clientProvider?.getClients()
      const firstClient = clients?.[0] ?? null
      if (firstClient) {
        setClient(firstClient)
        return true
      }
      return false
    }
    updateClient()
    const interval = setInterval(() => {
      // try to get `client` until successful
      if (updateClient()) {
        clearInterval(interval)
      }
    }, 500)
    return () => clearInterval(interval)
  }, [leanMonaco?.clientProvider])

  // Start RPC session
  useEffect(() => {
    function updateRpcSession() {
      if (rpcSess) return true
      if (!client || !uri) return false
      console.debug('rpc session connecting...')
      client.sendRequest('$/lean/rpc/connect', {uri: uri.toString()} as RpcConnectParams).then(result => {
        const sessionId = result.sessionId
        console.debug(`rpc session id: ${sessionId}`)
        const _rpcSess = new RpcSessionAtPos(client, sessionId, uri.toString())
        setRpcSess(_rpcSess)
      }).catch((err) => {
        console.debug("rpc connect failed: ", err)
      })
    }
    updateRpcSession()
    const interval = setInterval(() => {
      // try to get `rpcSess` until successful
      if (updateRpcSession()) {
        clearInterval(interval)
      }
    }, 500)
    return () => clearInterval(interval)
  }, [client, uri, rpcSess])

  // Select and highlight proof steps and corresponding hints
  // TODO: with the new design, there is no difference between the introduction and
  // a hint at the beginning of the proof...
  const [selectedStep, setSelectedStep] = useState<number>()

  useEffect (() => {
    // Lock editor mode
    if (levelInfo?.template) {

      if (model) {
        let code = model.getLinesContent()

        // TODO: It does seem that the template is always indented by spaces.
        // This is a hack, assuming there are exactly two.
        if (!code.join("").trim().length) {
          console.debug(`inserting template:\n${levelInfo?.template}`)
          // TODO: This does not work! HERE
          // Probably overwritten by a query to the server
          // DOC: REMOVED editor here
          editor?.executeEdits("template-writer", [{
            range: model.getFullModelRange(),
            text: levelInfo?.template + `\n`,
            forceMoveMarkers: true
          }])
        } else {
          console.debug(`not inserting template.`)
        }
      }
    } else {
    }
  }, [levelInfo, levelId, worldId, gameId, editor])


  useEffect(() => {
    // TODO: That's a problem if the saved proof contains an error
    // Reset command line input when loading a new level
    setTypewriterInput("")

  }, [gameId, worldId, levelId])

  useEffect(() => {
    const selection = editor?.getSelection();
    if (!typewriterMode && editor && selection) {
      // Delete last input attempt from command line
      editor.executeEdits("typewriter", [{
        range: selection,
        text: "",
        forceMoveMarkers: false
      }]);
      editor?.focus() // leanMonacoEditor?.editor.focus()
    }
  }, [typewriterMode])

  // useEffect(() => {
  //   // Forget whether hidden hints are displayed for steps that don't exist yet
  //   if (proof?.steps.length) {
  //     console.debug(Array.from(help))
  //     setHelp([...new Set(Array.from(help).filter(i => (i < proof?.steps.length)))])
  //   }
  // }, [proof])

  // // save showed help in store
  // useEffect(() => {
  //   if (proof?.steps.length) {
  //     console.debug(`showHelp:\n ${showHelp}`)
  //     setHelp(Array.from(showHelp))
  //   }
  // }, [showHelp])

  // Effect when command line mode gets enabled
  useEffect(() => {
    if (model && (typewriterMode)) {
      let code = model.getLinesContent().filter(line => line.trim())
      // REMOVED .editor call
      editor?.executeEdits("typewriter", [{
        range: model.getFullModelRange(),
        text: code.length ? code.join('\n') + '\n' : '',
        forceMoveMarkers: true
      }]);

      // let endPos = editor.getModel().getFullModelRange().getEndPosition()
      // if (editor.getModel().getLineContent(endPos.lineNumber).trim() !== "") {
      //   editor.executeEdits("typewriter", [{
      //     range: monaco.Selection.fromPositions(endPos, endPos),
      //     text: "\n",
      //     forceMoveMarkers: true
      //   }]);
      // }
      // let endPos = editor.getModel().getFullModelRange().getEndPosition()
      // let currPos = editor.getPosition()
      // if (currPos.column != 1 || (currPos.lineNumber != endPos.lineNumber && currPos.lineNumber != endPos.lineNumber - 1)) {
      //   // This is not a position that would naturally occur from Typewriter, reset:
      //   editor.setSelection(monaco.Selection.fromPositions(endPos, endPos))
      // }
    }
  }, [editor, typewriterMode, lockEditorMode]) // TODO: typewriterMode too?

  return <>
    { levelInfoIsLoading && <div className="app-content loading"><CircularProgress /></div>}
    <LevelAppBar
      pageNumber={pageNumber} setPageNumber={setPageNumber}
      isLoading={levelInfoIsLoading}
      levelTitle={(mobile ? "" : t("Level")) + ` ${levelId} / ${worldId ? gameInfo?.worldSize?.[worldId] ?? "" : ""}` +
        (levelInfo?.title && ` : ${gT(levelInfo?.title ?? "")}`)}
      />
    {mobile?
      // TODO: This is copied from the `Split` component below...
      <>
        <div className={`app-content level-mobile ${levelInfoIsLoading ? 'hidden' : ''}`}>
          <ExercisePanel codeviewRef={codeviewRef} visible={pageNumber == 0} />
          <InventoryPanel levelInfo={levelInfo} visible={pageNumber == 1} />
        </div>
      </>
    :
      <Split minSize={0} snapOffset={200} sizes={[25, 50, 25]} className={`app-content level ${levelInfoIsLoading ? 'hidden' : ''}`}>
        <ChatPanel lastLevel={lastLevel}/>
        <ExercisePanel codeviewRef={codeviewRef} />
        <InventoryPanel levelInfo={levelInfo} />
      </Split>
    }
  </>
}
