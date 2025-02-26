import * as React from 'react'
import { useEffect, useState, useRef, useContext } from 'react'
import { useSelector, useStore } from 'react-redux'
import Split from 'react-split'
import { useNavigate } from 'react-router-dom'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faHome, faArrowRight, faCode, faTerminal } from '@fortawesome/free-solid-svg-icons'
import { CircularProgress } from '@mui/material'
import type { Location } from 'vscode-languageserver-protocol'
import * as monaco from 'monaco-editor'
// import * as monaco from 'monaco-editor/esm/vs/editor/editor.api.js'
// import { AbbreviationProvider } from 'lean4web/client/src/editor/abbreviation/AbbreviationProvider'
// import { AbbreviationRewriter } from 'lean4web/client/src/editor/abbreviation/rewriter/AbbreviationRewriter'
// import { InfoProvider } from 'lean4web/client/src/editor/infoview'
// import { LeanTaskGutter } from 'lean4web/client/src/editor/taskgutter'
// import { InfoviewApi } from '@leanprover/infoview'
// import { EditorContext } from '../../../node_modules/lean4-infoview/src/infoview/contexts'
// import { EditorConnection, EditorEvents } from '../../../node_modules/lean4-infoview/src/infoview/editorConnection'
// import { EventEmitter } from '../../../node_modules/lean4-infoview/src/infoview/event'
// import { Diagnostic } from 'vscode-languageserver-types'
// import { DiagnosticSeverity } from 'vscode-languageclient';

import { useAppDispatch, useAppSelector } from '../hooks'
import { useGetGameInfoQuery, useLoadInventoryOverviewQuery, useLoadLevelQuery } from '../state/api'
import { changedSelection, codeEdited, selectCode, selectSelections, selectCompleted, helpEdited,
  selectHelp, selectDifficulty, selectInventory, selectTypewriterMode, changeTypewriterMode } from '../state/progress'
import { store } from '../state/store'
import {InventoryPanel} from './inventory'
import { ChatContext, InputModeContext, PreferencesContext, MonacoEditorContext,
  ProofContext, PageContext, GameIdContext } from '../state/context'
// import { DualEditor, ExerciseStatement } from './infoview/main'
// import { GameHint, InteractiveGoalsWithHints, ProofState } from './infoview/rpc_api'

import path from 'path';

import '@fontsource/roboto/300.css'
import '@fontsource/roboto/400.css'
import '@fontsource/roboto/500.css'
import '@fontsource/roboto/700.css'
// import 'lean4web/client/src/editor/infoview.css'
// import 'lean4web/client/src/editor/vscode.css'
import '../css/level.css'
// import { LeanClient } from 'lean4web/client/src/editor/leanclient'
// import { DisposingWebSocketMessageReader } from 'lean4web/client/src/reader'
// import { WebSocketMessageWriter, toSocket } from 'vscode-ws-jsonrpc'
// import { IConnectionProvider } from 'monaco-languageclient'
// import { monacoSetup } from 'lean4web/client/src/monacoSetup'
// import { onigasmH } from 'onigasm/lib/onigasmH'
// import { isLastStepWithErrors, lastStepHasErrors } from './infoview/goals'
import { InfoPopup } from './popup/info'
import { PreferencesPopup } from './popup/preferences'
import { useTranslation } from 'react-i18next'
import i18next from 'i18next'
import { ChatButtons } from './chat'
import { NavButton } from './navigation'
import { ExerciseStatement } from './editor/ExcerciseStatement'
import { Editor } from './editor/Editor'


export function NewLevel({visible = true}) {
  const dispatch = useAppDispatch()
  let { t } = useTranslation()
  const {gameId, worldId, levelId} = React.useContext(GameIdContext)
  const { mobile } = useContext(PreferencesContext)

  const [lockEditorMode, setLockEditorMode] = useState(false)

  const gameInfo = useGetGameInfoQuery({game: gameId})
  const levelInfo = useLoadLevelQuery({game: gameId, world: worldId, level: levelId})
  const typewriterMode = useSelector(selectTypewriterMode(gameId))

  const proofPanelRef = React.useRef<HTMLDivElement>(null)

  const setTypewriterMode = (newTypewriterMode: boolean) => dispatch(changeTypewriterMode({
    game: gameId,
    typewriterMode: newTypewriterMode
  }))

  // Load the namespace of the game
  i18next.loadNamespaces(gameId).catch(err => {
    console.warn(`translations for ${gameId} do not exist.`)
  })

  /** toggle input mode if allowed */
  function toggleInputMode(ev: React.MouseEvent) {
    if (!lockEditorMode) {
      setTypewriterMode(!typewriterMode)
      console.log('test')
    }
  }

  return <div className={`exercise${visible ? '' : ' hidden'}`}>
    { // Display world image if it exists.
      gameInfo.data?.worlds.nodes[worldId].image &&
      <div className='world-image'>
        <img className="contain" src={path.join("data", gameId, gameInfo.data?.worlds.nodes[worldId].image)} alt="" />
      </div>
    }
    { levelId > 0 &&
      <div className={`exercise-content ${(typewriterMode && !lockEditorMode) ? 'typewriter-mode': 'editor-mode' }`}>
        <NavButton
          className="btn-input-mode"
          icon={(typewriterMode && !lockEditorMode) ? faCode : faTerminal}
          inverted={true}
          disabled={levelId == 0 || lockEditorMode}
          onClick={(ev) => toggleInputMode(ev)}
          title={lockEditorMode ? t("Editor mode is enforced!") : typewriterMode ? t("Editor mode") : t("Typewriter mode")} />
        <div className="tmp-pusher" />
        <div className='proof' ref={proofPanelRef}>
          <ExerciseStatement showLeanStatement={!typewriterMode} />
          <Editor />
          {/* <div ref={editorRef} className="new-editor-test"/> */}
          {/* <div ref={infoviewRef} className="new-infoview-test"/> */}
          {/* <Level/> */}
          {/* { typewriterMode ? <Typewriter /> : <Editor /> } */}
        </div>
      </div>
    }
  </div>
}




// monacoSetup()

// export function Level({visible = true}) {
//   let { t } = useTranslation()


//   const {gameId, worldId, levelId} = React.useContext(GameIdContext)

//   // Load the namespace of the game
//   i18next.loadNamespaces(gameId).catch(err => {
//     console.warn(`translations for ${gameId} do not exist.`)
//   })

//   const gameInfo = useGetGameInfoQuery({game: gameId})
//   const levelInfo = useLoadLevelQuery({game: gameId, world: worldId, level: levelId})

//   const codeviewRef = useRef<HTMLDivElement>(null)

//   const dispatch = useAppDispatch()

//   const initialCode = useAppSelector(selectCode(gameId, worldId, levelId))
//   const initialSelections = useAppSelector(selectSelections(gameId, worldId, levelId))

//   const typewriterMode = useSelector(selectTypewriterMode(gameId))
//   const setTypewriterMode = (newTypewriterMode: boolean) => dispatch(changeTypewriterMode({game: gameId, typewriterMode: newTypewriterMode}))

//   const {deletedChat, setDeletedChat,showHelp, setShowHelp} = useContext(ChatContext)
//   const {proof, setProof} = useContext(ProofContext)

//   // Only for mobile layout
//   const {page, setPage} = useContext(PageContext)

//   // set to true to prevent switching between typewriter and editor
//   const [lockEditorMode, setLockEditorMode] = useState(false)
//   const [typewriterInput, setTypewriterInput] = useState("")
//   const lastLevel = levelId >= gameInfo.data?.worldSize[worldId]

//   // // impressum pop-up
//   // function toggleImpressum() {setImpressum(!impressum)}
//   // function togglePrivacy() {setPrivacy(!privacy)}

//   // When clicking on an inventory item, the inventory is overlayed by the item's doc.
//   // If this state is set to a pair `(name, type)` then the according doc will be open.
//   // Set `inventoryDoc` to `null` to close the doc
//   const [inventoryDoc, setInventoryDoc] = useState<{name: string, type: string}>(null)
//   function closeInventoryDoc () {setInventoryDoc(null)}

//   const onDidChangeContent = (code) => {
//     dispatch(codeEdited({game: gameId, world: worldId, level: levelId, code}))
//   }

//   const onDidChangeSelection = (monacoSelections) => {
//     const selections = monacoSelections.map(
//       ({selectionStartLineNumber, selectionStartColumn, positionLineNumber, positionColumn}) =>
//       {return {selectionStartLineNumber, selectionStartColumn, positionLineNumber, positionColumn}})
//     dispatch(changedSelection({game: gameId, world: worldId, level: levelId, selections}))
//   }


//   // const {editor, infoProvider, editorConnection} =
//   //   useLevelEditor(codeviewRef, initialCode, initialSelections, onDidChangeContent, onDidChangeSelection)

//   // /** Unused. Was implementing an undo button, which has been replaced by `deleteProof` inside
//   //  * `TypewriterInterface`.
//   //  */
//   // const handleUndo = () => {
//   //   const endPos = editor.getModel().getFullModelRange().getEndPosition()
//   //   let range
//   //   console.log(endPos.column)
//   //   if (endPos.column === 1) {
//   //     range = monaco.Selection.fromPositions(
//   //       new monaco.Position(endPos.lineNumber - 1, 1),
//   //       endPos
//   //     )
//   //   } else {
//   //     range = monaco.Selection.fromPositions(
//   //       new monaco.Position(endPos.lineNumber, 1),
//   //       endPos
//   //     )
//   //   }
//   //   editor.executeEdits("undo-button", [{
//   //     range,
//   //     text: "",
//   //     forceMoveMarkers: false
//   //   }]);
//   // }

//   // Select and highlight proof steps and corresponding hints
//   // TODO: with the new design, there is no difference between the introduction and
//   // a hint at the beginning of the proof...
//   const [selectedStep, setSelectedStep] = useState<number>()


//   // useEffect (() => {
//   //   // Lock editor mode
//   //   if (levelInfo.data?.template) {
//   //     setLockEditorMode(true)

//   //     if (editor) {
//   //       let code = editor.getModel().getLinesContent()

//   //       // console.log(`insert. code: ${code}`)
//   //       // console.log(`insert. join: ${code.join('')}`)
//   //       // console.log(`insert. trim: ${code.join('').trim()}`)
//   //       // console.log(`insert. length: ${code.join('').trim().length}`)
//   //       // console.log(`insert. range: ${editor.getModel().getFullModelRange()}`)


//   //       // TODO: It does seem that the template is always indented by spaces.
//   //       // This is a hack, assuming there are exactly two.
//   //       if (!code.join('').trim().length) {
//   //         console.debug(`inserting template:\n${levelInfo.data.template}`)
//   //         // TODO: This does not work! HERE
//   //         // Probably overwritten by a query to the server
//   //         editor.executeEdits("template-writer", [{
//   //           range: editor.getModel().getFullModelRange(),
//   //           text: levelInfo.data.template + `\n`,
//   //           forceMoveMarkers: true
//   //         }])
//   //       } else {
//   //         console.debug(`not inserting template.`)
//   //       }
//   //     }
//   //   } else {
//   //     setLockEditorMode(false)
//   //   }
//   // }, [levelInfo, levelId, worldId, gameId, editor])


//   // useEffect(() => {
//   //   // TODO: That's a problem if the saved proof contains an error
//   //   // Reset command line input when loading a new level
//   //   setTypewriterInput("")

//   //   // Load the selected help steps from the store
//   //   setShowHelp(new Set(selectHelp(gameId, worldId, levelId)(store.getState())))
//   // }, [gameId, worldId, levelId])

//   // useEffect(() => {
//   //   if (!(typewriterMode && !lockEditorMode) && editor) {
//   //     // Delete last input attempt from command line
//   //     editor.executeEdits("typewriter", [{
//   //       range: editor.getSelection(),
//   //       text: "",
//   //       forceMoveMarkers: false
//   //     }]);
//   //     editor.focus()
//   //   }
//   // }, [typewriterMode, lockEditorMode])

//   useEffect(() => {
//     // Forget whether hidden hints are displayed for steps that don't exist yet
//     if (proof?.steps.length) {
//       console.debug(Array.from(showHelp))
//       setShowHelp(new Set(Array.from(showHelp).filter(i => (i < proof?.steps.length))))
//     }
//   }, [proof])

//   // save showed help in store
//   useEffect(() => {
//     if (proof?.steps.length) {
//       console.debug(`showHelp:\n ${showHelp}`)
//       dispatch(helpEdited({game: gameId, world: worldId, level: levelId, help: Array.from(showHelp)}))
//     }
//   }, [showHelp])

//   // Effect when command line mode gets enabled
//   // useEffect(() => {
//   //   if (//onigasmH &&
//   //       editor && (typewriterMode && !lockEditorMode)) {
//   //     let code = editor.getModel().getLinesContent().filter(line => line.trim())
//   //     editor.executeEdits("typewriter", [{
//   //       range: editor.getModel().getFullModelRange(),
//   //       text: code.length ? code.join('\n') + '\n' : '',
//   //       forceMoveMarkers: true
//   //     }]);

//       // let endPos = editor.getModel().getFullModelRange().getEndPosition()
//       // if (editor.getModel().getLineContent(endPos.lineNumber).trim() !== "") {
//       //   editor.executeEdits("typewriter", [{
//       //     range: monaco.Selection.fromPositions(endPos, endPos),
//       //     text: "\n",
//       //     forceMoveMarkers: true
//       //   }]);
//       // }
//       // let endPos = editor.getModel().getFullModelRange().getEndPosition()
//       // let currPos = editor.getPosition()
//       // if (currPos.column != 1 || (currPos.lineNumber != endPos.lineNumber && currPos.lineNumber != endPos.lineNumber - 1)) {
//       //   // This is not a position that would naturally occur from Typewriter, reset:
//       //   editor.setSelection(monaco.Selection.fromPositions(endPos, endPos))
//       // }
//     // }
//   // }, [editor, typewriterMode, lockEditorMode, ])//onigasmH == null])


//   return <div className={visible?'':'hidden'}>
//       {/* <div style={levelInfo.isLoading ? null : {display: "none"}} className="app-content loading"><CircularProgress /></div> */}
//               {/* <EditorContext.Provider value={editorConnection}>
//                 <MonacoEditorContext.Provider value={editor}> */}
//                     {levelId > 0 &&
//                     <ExercisePanel codeviewRef={codeviewRef} />}
//                 {/* </MonacoEditorContext.Provider>
//               </EditorContext.Provider> */}
//   </div>
// }

//

// </MonacoEditorContext.Provider>
// </EditorContext.Provider>



// export function ExercisePanel({codeviewRef, visible=true}: {codeviewRef: React.MutableRefObject<HTMLDivElement>, visible?: boolean}) {
//   const {gameId, worldId, levelId} = React.useContext(GameIdContext)
//   const level = useLoadLevelQuery({game: gameId, world: worldId, level: levelId})
//   const gameInfo = useGetGameInfoQuery({game: gameId})
//   return <div className={`exercise-panel ${visible ? '' : 'hidden'}`}>
//     <div className="">
//       {/* <DualEditor level={level?.data} codeviewRef={codeviewRef} levelId={levelId} worldId={worldId} worldSize={gameInfo.data?.worldSize[worldId]}/> */}
//     </div>
//   </div>
// }


//   <Split minSize={0} snapOffset={200} sizes={[25, 75]} className={`app-content level ${level.isLoading ? 'hidden' : ''}`}>
//   <ChatPanel lastLevel={lastLevel}/>
//   <InventoryPanel />
//   </Split>

// function IntroductionPanel({gameInfo}) {
//   let { t } = useTranslation()
//   const {gameId, worldId} = React.useContext(GameIdContext)
//   const {mobile} = React.useContext(PreferencesContext)

//   let text: Array<string> = t(gameInfo.data?.worlds.nodes[worldId].introduction, {ns: gameId}).split(/\n(\s*\n)+/)

//   return <div className="chat-panel">
//     <div className="chat">
//       {text?.filter(t => t.trim()).map(((t, i) =>
//         <Hint key={`intro-p-${i}`}
//           hint={{text: t, hidden: false, rawText: t, varNames: []}} step={0} selected={null} toggleSelection={undefined} />
//       ))}
//     </div>
//     <ChatButtons />
//   </div>
// }

// /** The site with the introduction text of a world */
// function Introduction() {
//   let { t } = useTranslation()

//   const {gameId, worldId} = React.useContext(GameIdContext)
//   const {mobile} = useContext(PreferencesContext)

//   const inventory = useLoadInventoryOverviewQuery({game: gameId})

//   const gameInfo = useGetGameInfoQuery({game: gameId})


//   let image: string = gameInfo.data?.worlds.nodes[worldId].image


//   // const toggleImpressum = () => {
//   //   setImpressum(!impressum)
//   // }
//   // const togglePrivacy = () => {
//   //   setPrivacy(!privacy)
//   // }
//   return <>
//     {/* <LevelAppBar isLoading={gameInfo.isLoading} levelTitle={t("Introduction")} toggleImpressum={toggleImpressum} togglePrivacy={togglePrivacy} toggleInfo={toggleInfo} togglePreferencesPopup={togglePreferencesPopup}/> */}
//     {gameInfo.isLoading ?
//       <div className="app-content loading"><CircularProgress /></div>
//     : mobile ?
//         <IntroductionPanel gameInfo={gameInfo} />
//       :
//         // <Split minSize={0} snapOffset={200} sizes={[25, 50, 25]} className={`app-content level`}>
//         //   <IntroductionPanel gameInfo={gameInfo} />
//           <div className="world-image-container empty center">
//             {image &&
//               <img className="contain" src={path.join("data", gameId, image)} alt="" />
//             }

//           </div>
//           // {/* <InventoryPanel /> */}
//         // </Split>
//       }

//   </>
// }

// {mobile?
//   // TODO: This is copied from the `Split` component below...
//   <>
//     <div className={`app-content level-mobile ${level.isLoading ? 'hidden' : ''}`}>
//       <ExercisePanel
//         impressum={impressum}
//         closeImpressum={closeImpressum}
//         codeviewRef={codeviewRef}
//         visible={pageNumber == 0} />
//       <InventoryPanel levelInfo={level?.data} visible={pageNumber == 1} />
//     </div>
//   </>
// :
//   <Split minSize={0} snapOffset={200} sizes={[25, 50, 25]} className={`app-content level ${level.isLoading ? 'hidden' : ''}`}>
//     <ChatPanel lastLevel={lastLevel}/>
//     <ExercisePanel
//       impressum={impressum}
//       closeImpressum={closeImpressum}
//       codeviewRef={codeviewRef} />
//     <InventoryPanel levelInfo={level?.data} />
//   </Split>
// }

// function useLevelEditor(codeviewRef, initialCode, initialSelections, onDidChangeContent, onDidChangeSelection) {

//   const {gameId, worldId, levelId} = React.useContext(GameIdContext)

//   const [editor, setEditor] = useState<monaco.editor.IStandaloneCodeEditor|null>(null)
//   const [infoProvider, setInfoProvider] = useState<null|InfoProvider>(null)
//   const [editorConnection, setEditorConnection] = useState<null|EditorConnection>(null)

//   const uriStr = `file:///${worldId}/${levelId}`
//   const uri = monaco.Uri.parse(uriStr)

//   const inventory: Array<String> = useSelector(selectInventory(gameId))
//   const difficulty: number = useSelector(selectDifficulty(gameId))

//   useEffect(() => {
//     // monaco.editor.getModels().forEach(model => model.dispose());

//     console.info(`trying to create model: ${gameId} ${worldId} ${levelId} ${uri}`)
//     const model = monaco.editor.createModel(initialCode ?? '', 'lean4', uri)
//     if (onDidChangeContent) {
//       model.onDidChangeContent(() => onDidChangeContent(model.getValue()))
//     }

//     const editor = monaco.editor.create(codeviewRef.current!, {
//       model,
//       glyphMargin: true,
//       quickSuggestions: false,
//       lineDecorationsWidth: 5,
//       folding: false,
//       lineNumbers: 'on',
//       lightbulb: {
//         enabled: true
//       },
//       unicodeHighlight: {
//           ambiguousCharacters: false,
//       },
//       automaticLayout: true,
//       minimap: {
//         enabled: false
//       },
//       lineNumbersMinChars: 3,
//       tabSize: 2,
//       'semanticHighlighting.enabled': true,
//       fontFamily: "JuliaMono",
//       theme: 'vs-code-theme-converted'
//     })
//     if (onDidChangeSelection) {
//       editor.onDidChangeCursorSelection(() => onDidChangeSelection(editor.getSelections()))
//     }
//     if (initialSelections) {
//       console.debug("Initial Selection: ", initialSelections)
//       // BUG: Somehow I get an `invalid arguments` bug here
//       // editor.setSelections(initialSelections)
//     }
//     setEditor(editor)
//     const abbrevRewriter = new AbbreviationRewriter(new AbbreviationProvider(), model, editor)

//     const socketUrl = ((window.location.protocol === "https:") ? "wss://" : "ws://") + window.location.host + '/websocket/' + gameId

//     const connectionProvider : IConnectionProvider = {
//       get: async () => {
//         return await new Promise((resolve, reject) => {
//           console.log(`connecting ${socketUrl}`)
//           const websocket = new WebSocket(socketUrl)
//           websocket.addEventListener('error', (ev) => {
//             reject(ev)
//           })
//           websocket.addEventListener('message', (msg) => {
//             // console.log(msg.data)
//           })
//           websocket.addEventListener('open', () => {
//             const socket = toSocket(websocket)
//             const reader = new DisposingWebSocketMessageReader(socket)
//             const writer = new WebSocketMessageWriter(socket)
//             resolve({
//               reader,
//               writer
//             })
//           })
//         })
//       }
//     }

//     // Following `vscode-lean4/webview/index.ts`
//     const client = new LeanClient(connectionProvider, showRestartMessage, {inventory, difficulty})
//     const infoProvider = new InfoProvider(client)
//     // const div: HTMLElement = infoviewRef.current!
//     const imports = {
//       '@leanprover/infoview': `${window.location.origin}/index.production.min.js`,
//       'react': `${window.location.origin}/react.production.min.js`,
//       'react/jsx-runtime': `${window.location.origin}/react-jsx-runtime.production.min.js`,
//       'react-dom': `${window.location.origin}/react-dom.production.min.js`,
//       'react-popper': `${window.location.origin}/react-popper.production.min.js`
//     }
//     // loadRenderInfoview(imports, [infoProvider.getApi(), div], setInfoviewApi)
//     setInfoProvider(infoProvider)

//     // TODO: it looks like we get errors "File Changed" here.
//     client.restart("Lean4Game")

//     const editorApi = infoProvider.getApi()

//     const editorEvents: EditorEvents = {
//         initialize: new EventEmitter(),
//         gotServerNotification: new EventEmitter(),
//         sentClientNotification: new EventEmitter(),
//         serverRestarted: new EventEmitter(),
//         serverStopped: new EventEmitter(),
//         changedCursorLocation: new EventEmitter(),
//         changedInfoviewConfig: new EventEmitter(),
//         runTestScript: new EventEmitter(),
//         requestedAction: new EventEmitter(),
//     };

//     // Challenge: write a type-correct fn from `Eventify<T>` to `T` without using `any`
//     const infoviewApi: InfoviewApi = {
//         initialize: async l => editorEvents.initialize.fire(l),
//         gotServerNotification: async (method, params) => {
//             editorEvents.gotServerNotification.fire([method, params]);
//         },
//         sentClientNotification: async (method, params) => {
//             editorEvents.sentClientNotification.fire([method, params]);
//         },
//         serverRestarted: async r => editorEvents.serverRestarted.fire(r),
//         serverStopped: async serverStoppedReason => {
//             editorEvents.serverStopped.fire(serverStoppedReason)
//         },
//         changedCursorLocation: async loc => editorEvents.changedCursorLocation.fire(loc),
//         changedInfoviewConfig: async conf => editorEvents.changedInfoviewConfig.fire(conf),
//         requestedAction: async action => editorEvents.requestedAction.fire(action),
//         // See https://rollupjs.org/guide/en/#avoiding-eval
//         // eslint-disable-next-line @typescript-eslint/no-implied-eval
//         runTestScript: async script => new Function(script)(),
//         getInfoviewHtml: async () => document.body.innerHTML,
//     };

//     const ec = new EditorConnection(editorApi, editorEvents);
//     setEditorConnection(ec)

//     editorEvents.initialize.on((loc: Location) => ec.events.changedCursorLocation.fire(loc))

//     setEditor(editor)
//     setInfoProvider(infoProvider)

//     infoProvider.openPreview(editor, infoviewApi)
//     const taskgutter = new LeanTaskGutter(infoProvider.client, editor)

//     // TODO:
//     // setRestart(() => restart)

//     return () => {
//       editor.dispose();
//       model.dispose();
//       abbrevRewriter.dispose();
//       taskgutter.dispose();
//       infoProvider.dispose();
//       client.dispose();
//     }
//   }, [gameId, worldId, levelId])

//   const showRestartMessage = () => {
//     // setRestartMessage(true)
//     console.log("TODO: SHOW RESTART MESSAGE")
//   }

//   return {editor, infoProvider, editorConnection}
// }
