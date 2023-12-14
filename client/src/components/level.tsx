import * as React from 'react'
import { useEffect, useState, useRef, useContext } from 'react'
import { useSelector, useStore } from 'react-redux'
import Split from 'react-split'
import { useParams } from 'react-router-dom'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faHome, faArrowRight } from '@fortawesome/free-solid-svg-icons'
import { CircularProgress } from '@mui/material'
import type { Location } from 'vscode-languageserver-protocol'
import * as monaco from 'monaco-editor/esm/vs/editor/editor.api.js'
import { AbbreviationProvider } from 'lean4web/client/src/editor/abbreviation/AbbreviationProvider'
import { AbbreviationRewriter } from 'lean4web/client/src/editor/abbreviation/rewriter/AbbreviationRewriter'
import { InfoProvider } from 'lean4web/client/src/editor/infoview'
import { LeanTaskGutter } from 'lean4web/client/src/editor/taskgutter'
import { InfoviewApi } from '@leanprover/infoview'
import { EditorContext } from '../../../node_modules/lean4-infoview/src/infoview/contexts'
import { EditorConnection, EditorEvents } from '../../../node_modules/lean4-infoview/src/infoview/editorConnection'
import { EventEmitter } from '../../../node_modules/lean4-infoview/src/infoview/event'

import { GameIdContext } from '../app'
import { ConnectionContext, connection, useLeanClient } from '../connection'
import { useAppDispatch, useAppSelector } from '../hooks'
import { useGetGameInfoQuery, useLoadInventoryOverviewQuery, useLoadLevelQuery } from '../state/api'
import { changedSelection, codeEdited, selectCode, selectSelections, selectCompleted, helpEdited,
  selectHelp, selectDifficulty, selectInventory, selectTypewriterMode, changeTypewriterMode } from '../state/progress'
import { store } from '../state/store'
import { Button } from './button'
import Markdown from './markdown'
import {InventoryPanel} from './inventory'
import { hasInteractiveErrors } from './infoview/typewriter'
import { DeletedChatContext, InputModeContext, MobileContext, MonacoEditorContext,
  ProofContext, ProofStep, SelectionContext, WorldLevelIdContext } from './infoview/context'
import { DualEditor } from './infoview/main'
import { GameHint } from './infoview/rpc_api'
import { DeletedHints, Hint, Hints, filterHints } from './hints'
import { PrivacyPolicyPopup } from './popup/privacy_policy'
import path from 'path';

import '@fontsource/roboto/300.css'
import '@fontsource/roboto/400.css'
import '@fontsource/roboto/500.css'
import '@fontsource/roboto/700.css'
import 'lean4web/client/src/editor/infoview.css'
import 'lean4web/client/src/editor/vscode.css'
import '../css/level.css'
import { LevelAppBar } from './app_bar'

function Level() {
  const params = useParams()
  const levelId = parseInt(params.levelId)
  const worldId = params.worldId

  const [impressum, setImpressum] = React.useState(false)

  const closeImpressum = () => {
    setImpressum(false)
  }

  return <WorldLevelIdContext.Provider value={{worldId, levelId}}>
    {levelId == 0 ?
      <Introduction impressum={impressum} setImpressum={setImpressum} /> :
      <PlayableLevel key={`${worldId}/${levelId}`} impressum={impressum} setImpressum={setImpressum} />}
    {impressum ? <PrivacyPolicyPopup handleClose={closeImpressum} /> : null}
  </WorldLevelIdContext.Provider>
}

function ChatPanel({lastLevel}) {
  const chatRef = useRef<HTMLDivElement>(null)
  const {mobile} = useContext(MobileContext)
  const gameId = useContext(GameIdContext)
  const {worldId, levelId} = useContext(WorldLevelIdContext)
  const level = useLoadLevelQuery({game: gameId, world: worldId, level: levelId})
  const {proof, setProof} = useContext(ProofContext)
  const {deletedChat, setDeletedChat, showHelp, setShowHelp} = useContext(DeletedChatContext)
  const {selectedStep, setSelectedStep} = useContext(SelectionContext)
  const completed = useAppSelector(selectCompleted(gameId, worldId, levelId))

  // If the last step has errors, we want to treat it as if it is part of the second-to-last step
  let k = proof.length - 1
  let withErr = hasInteractiveErrors(proof[k]?.errors) ? 1 : 0

  function toggleSelection(line: number) {
    return (ev) => {
      console.debug('toggled selection')
      if (selectedStep == line) {
        setSelectedStep(undefined)
      } else {
        setSelectedStep(line)
      }
    }
  }

  function hasHiddenHints(i : number): boolean {
    let step = proof[i]
    // For example if the proof isn't loaded yet
    if(!step) {return false}
    return step.hints.some((hint) => hint.hidden)
  }

  const activateHiddenHints = (ev) => {
    // If the last step (`k`) has errors, we want the hidden hints from the
    // second-to-last step to be affected
    if (!(proof.length)) {return}

    // state must not be mutated, therefore we need to clone the set
    let tmp = new Set(showHelp)
    if (tmp.has(k - withErr)) {
      tmp.delete(k - withErr)
    } else {
      tmp.add(k - withErr)
    }
    setShowHelp(tmp)
    console.debug(`help: ${Array.from(tmp.values())}`)
  }

  useEffect(() => {
    // TODO: For some reason this is always called twice
    console.debug('scroll chat')
    if (!mobile) {
      chatRef.current!.lastElementChild?.scrollIntoView() //scrollTo(0,0)
    }
  }, [proof, showHelp])

  // Scroll to element if selection changes
  useEffect(() => {
    if (typeof selectedStep !== 'undefined') {
      Array.from(chatRef.current?.getElementsByClassName(`step-${selectedStep}`)).map((elem) => {
        elem.scrollIntoView({block: "center"})
      })
    }
  }, [selectedStep])

  // useEffect(() => {
  //   // // Scroll to top when loading a new level
  //   // // TODO: Thats the wrong behaviour probably
  //   // chatRef.current!.scrollTo(0,0)
  // }, [gameId, worldId, levelId])

  let introText: Array<string> = level?.data?.introduction.split(/\n(\s*\n)+/)

  // experimental: Remove all hints that appeared identically in the previous step
  // This effectively prevent consequtive hints being shown.
  let modifiedHints : GameHint[][] = filterHints(proof)

  return <div className="chat-panel">
    <div ref={chatRef} className="chat">
      {introText?.filter(t => t.trim()).map(((t, i) =>
        // Show the level's intro text as hints, too
        <Hint key={`intro-p-${i}`}
          hint={{text: t, hidden: false}} step={0} selected={selectedStep} toggleSelection={toggleSelection(0)} />
      ))}
      {modifiedHints.map((step, i) => {
        // It the last step has errors, it will have the same hints
        // as the second-to-last step. Therefore we should not display them.
        if (!(i == proof.length - 1 && withErr)) {
          // TODO: Should not use index as key.
          return <Hints key={`hints-${i}`}
            hints={step} showHidden={showHelp.has(i)} step={i}
            selected={selectedStep} toggleSelection={toggleSelection(i)} lastLevel={i == proof.length - 1}/>
        }
      })}
      <DeletedHints hints={deletedChat}/>
      {completed &&
        <>
          <div className={`message information recent step-${k}${selectedStep == k ? ' selected' : ''}`} onClick={toggleSelection(k)}>
            Level completed! 🎉
          </div>
          {level?.data?.conclusion?.trim() &&
            <div className={`message information recent step-${k}${selectedStep == k ? ' selected' : ''}`} onClick={toggleSelection(k)}>
              <Markdown>{level?.data?.conclusion}</Markdown>
            </div>
          }
        </>
      }
    </div>
    <div className="button-row">
      {completed && (lastLevel ?
        <Button to={`/${gameId}`}>
          <FontAwesomeIcon icon={faHome} />&nbsp;Leave World
        </Button> :
        <Button to={`/${gameId}/world/${worldId}/level/${levelId + 1}`}>
          Next&nbsp;<FontAwesomeIcon icon={faArrowRight} />
        </Button>)
        }
      {hasHiddenHints(proof.length - 1) && !showHelp.has(k - withErr) &&
        <Button to="" onClick={activateHiddenHints}>
          Show more help!
        </Button>
      }
    </div>
  </div>
}

function ExercisePanel({codeviewRef, visible=true}) {
  const gameId = React.useContext(GameIdContext)
  const {worldId, levelId} = useContext(WorldLevelIdContext)
  const level = useLoadLevelQuery({game: gameId, world: worldId, level: levelId})
  const gameInfo = useGetGameInfoQuery({game: gameId})
  return <div className={`exercise-panel ${visible ? '' : 'hidden'}`}>
    <div className="exercise">
      <DualEditor level={level?.data} codeviewRef={codeviewRef} levelId={levelId} worldId={worldId} worldSize={gameInfo.data?.worldSize[worldId]}/>
    </div>
  </div>
}

function PlayableLevel({impressum, setImpressum}) {
  const codeviewRef = useRef<HTMLDivElement>(null)
  const gameId = React.useContext(GameIdContext)
  const {worldId, levelId} = useContext(WorldLevelIdContext)
  const {mobile} = React.useContext(MobileContext)

  const dispatch = useAppDispatch()

  const difficulty = useSelector(selectDifficulty(gameId))
  const initialCode = useAppSelector(selectCode(gameId, worldId, levelId))
  const initialSelections = useAppSelector(selectSelections(gameId, worldId, levelId))
  const inventory: Array<String> = useSelector(selectInventory(gameId))

  const typewriterMode = useSelector(selectTypewriterMode(gameId))
  const setTypewriterMode = (newTypewriterMode: boolean) => dispatch(changeTypewriterMode({game: gameId, typewriterMode: newTypewriterMode}))

  const gameInfo = useGetGameInfoQuery({game: gameId})
  const level = useLoadLevelQuery({game: gameId, world: worldId, level: levelId})

  // The state variables for the `ProofContext`
  const [proof, setProof] = useState<Array<ProofStep>>([])
  // When deleting the proof, we want to keep to old messages around until
  // a new proof has been entered. e.g. to consult messages coming from dead ends
  const [deletedChat, setDeletedChat] = useState<Array<GameHint>>([])
  // A set of row numbers where help is displayed
  const [showHelp, setShowHelp] = useState<Set<number>>(new Set())
  // Only for mobile layout
  const [pageNumber, setPageNumber] = useState(0)

  // set to true to prevent switching between typewriter and editor
  const [lockInputMode, setLockInputMode] = useState(false)
  const [typewriterInput, setTypewriterInput] = useState("")
  const lastLevel = levelId >= gameInfo.data?.worldSize[worldId]

  // impressum pop-up
  function toggleImpressum() {setImpressum(!impressum)}

  // When clicking on an inventory item, the inventory is overlayed by the item's doc.
  // If this state is set to a pair `(name, type)` then the according doc will be open.
  // Set `inventoryDoc` to `null` to close the doc
  const [inventoryDoc, setInventoryDoc] = useState<{name: string, type: string}>(null)
  function closeInventoryDoc () {setInventoryDoc(null)}



  const onDidChangeContent = (code) => {
    dispatch(codeEdited({game: gameId, world: worldId, level: levelId, code}))
  }

  const onDidChangeSelection = (monacoSelections) => {
    const selections = monacoSelections.map(
      ({selectionStartLineNumber, selectionStartColumn, positionLineNumber, positionColumn}) =>
      {return {selectionStartLineNumber, selectionStartColumn, positionLineNumber, positionColumn}})
    dispatch(changedSelection({game: gameId, world: worldId, level: levelId, selections}))
  }


  const {editor, infoProvider, editorConnection} =
    useLevelEditor(codeviewRef, initialCode, initialSelections, onDidChangeContent, onDidChangeSelection)

  /** Unused. Was implementing an undo button, which has been replaced by `deleteProof` inside
   * `TypewriterInterface`.
   */
  const handleUndo = () => {
    const endPos = editor.getModel().getFullModelRange().getEndPosition()
    let range
    console.log(endPos.column)
    if (endPos.column === 1) {
      range = monaco.Selection.fromPositions(
        new monaco.Position(endPos.lineNumber - 1, 1),
        endPos
      )
    } else {
      range = monaco.Selection.fromPositions(
        new monaco.Position(endPos.lineNumber, 1),
        endPos
      )
    }
    editor.executeEdits("undo-button", [{
      range,
      text: "",
      forceMoveMarkers: false
    }]);
  }

  // Select and highlight proof steps and corresponding hints
  // TODO: with the new design, there is no difference between the introduction and
  // a hint at the beginning of the proof...
  const [selectedStep, setSelectedStep] = useState<number>()

  // if the user inventory changes, notify the server
  useEffect(() => {
    let leanClient = connection.getLeanClient(gameId)
    leanClient.sendNotification('$/game/setInventory', {inventory: inventory, difficulty: difficulty})
  }, [inventory])

  useEffect (() => {
    // Lock editor mode
    if (level?.data?.template) {
      setTypewriterMode(false)

      if (editor) {
        let code = editor.getModel().getLinesContent()

        // console.log(`insert. code: ${code}`)
        // console.log(`insert. join: ${code.join('')}`)
        // console.log(`insert. trim: ${code.join('').trim()}`)
        // console.log(`insert. length: ${code.join('').trim().length}`)
        // console.log(`insert. range: ${editor.getModel().getFullModelRange()}`)


        // TODO: It does seem that the template is always indented by spaces.
        // This is a hack, assuming there are exactly two.
        if (!code.join('').trim().length) {
          console.debug(`inserting template:\n${level.data.template}`)
          // TODO: This does not work! HERE
          // Probably overwritten by a query to the server
          editor.executeEdits("template-writer", [{
            range: editor.getModel().getFullModelRange(),
            text: level.data.template + `\n`,
            forceMoveMarkers: true
          }])
        } else {
          console.debug(`not inserting template.`)
        }
      }
    }
  }, [level, levelId, worldId, gameId, editor])


  useEffect(() => {
    // TODO: That's a problem if the saved proof contains an error
    // Reset command line input when loading a new level
    setTypewriterInput("")

    // Load the selected help steps from the store
    setShowHelp(new Set(selectHelp(gameId, worldId, levelId)(store.getState())))
  }, [gameId, worldId, levelId])

  useEffect(() => {
    if (!typewriterMode && editor) {
      // Delete last input attempt from command line
      editor.executeEdits("typewriter", [{
        range: editor.getSelection(),
        text: "",
        forceMoveMarkers: false
      }]);
      editor.focus()
    }
  }, [typewriterMode])

  useEffect(() => {
    // Forget whether hidden hints are displayed for steps that don't exist yet
    if (proof.length) {
      console.debug(Array.from(showHelp))
      setShowHelp(new Set(Array.from(showHelp).filter(i => (i < proof.length))))
    }
  }, [proof])

  // save showed help in store
  useEffect(() => {
    if (proof.length) {
      console.debug(`showHelp:\n ${showHelp}`)
      dispatch(helpEdited({game: gameId, world: worldId, level: levelId, help: Array.from(showHelp)}))
    }
  }, [showHelp])

  // Effect when command line mode gets enabled
  useEffect(() => {
    if (editor && typewriterMode) {
      let code = editor.getModel().getLinesContent().filter(line => line.trim())
      editor.executeEdits("typewriter", [{
        range: editor.getModel().getFullModelRange(),
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
  }, [editor, typewriterMode])

  return <>
    <div style={level.isLoading ? null : {display: "none"}} className="app-content loading"><CircularProgress /></div>
    <DeletedChatContext.Provider value={{deletedChat, setDeletedChat, showHelp, setShowHelp}}>
      <SelectionContext.Provider value={{selectedStep, setSelectedStep}}>
        <InputModeContext.Provider value={{typewriterMode, setTypewriterMode, typewriterInput, setTypewriterInput, lockInputMode, setLockInputMode}}>
          <ProofContext.Provider value={{proof, setProof}}>
            <EditorContext.Provider value={editorConnection}>
              <MonacoEditorContext.Provider value={editor}>
                <LevelAppBar
                  pageNumber={pageNumber} setPageNumber={setPageNumber}
                  isLoading={level.isLoading}
                  levelTitle={`${mobile ? '' : 'Level '}${levelId} / ${gameInfo.data?.worldSize[worldId]}` +
                    (level?.data?.title && ` : ${level?.data?.title}`)}
                  toggleImpressum={toggleImpressum} />
                {mobile?
                  // TODO: This is copied from the `Split` component below...
                  <>
                    <div className={`app-content level-mobile ${level.isLoading ? 'hidden' : ''}`}>
                      <ExercisePanel
                        codeviewRef={codeviewRef}
                        visible={pageNumber == 0} />
                      <InventoryPanel levelInfo={level?.data} visible={pageNumber == 1} />
                    </div>
                  </>
                :
                  <Split minSize={0} snapOffset={200} sizes={[25, 50, 25]} className={`app-content level ${level.isLoading ? 'hidden' : ''}`}>
                    <ChatPanel lastLevel={lastLevel}/>
                    <ExercisePanel
                      codeviewRef={codeviewRef} />
                    <InventoryPanel levelInfo={level?.data} />
                  </Split>
                }
              </MonacoEditorContext.Provider>
            </EditorContext.Provider>
          </ProofContext.Provider>
        </InputModeContext.Provider>
      </SelectionContext.Provider>
    </DeletedChatContext.Provider>
  </>
}

function IntroductionPanel({gameInfo}) {
  const gameId = React.useContext(GameIdContext)
  const {worldId} = useContext(WorldLevelIdContext)
  const {mobile} = React.useContext(MobileContext)

  let text: Array<string> = gameInfo.data?.worlds.nodes[worldId].introduction.split(/\n(\s*\n)+/)

  return <div className="chat-panel">
    <div className="chat">
      {text?.filter(t => t.trim()).map(((t, i) =>
        <Hint key={`intro-p-${i}`}
          hint={{text: t, hidden: false}} step={0} selected={null} toggleSelection={undefined} />
      ))}
    </div>
    <div className={`button-row${mobile ? ' mobile' : ''}`}>
      {gameInfo.data?.worldSize[worldId] == 0 ?
        <Button to={`/${gameId}`}><FontAwesomeIcon icon={faHome} /></Button> :
        <Button to={`/${gameId}/world/${worldId}/level/1`}>
          Start&nbsp;<FontAwesomeIcon icon={faArrowRight} />
        </Button>
      }
    </div>
  </div>
}

export default Level

/** The site with the introduction text of a world */
function Introduction({impressum, setImpressum}) {
  const gameId = React.useContext(GameIdContext)
  const {mobile} = useContext(MobileContext)

  const inventory = useLoadInventoryOverviewQuery({game: gameId})

  const gameInfo = useGetGameInfoQuery({game: gameId})

  const {worldId} = useContext(WorldLevelIdContext)

  let image: string = gameInfo.data?.worlds.nodes[worldId].image


  const toggleImpressum = () => {
    setImpressum(!impressum)
  }

  return <>
    <LevelAppBar isLoading={gameInfo.isLoading} levelTitle="Introduction" toggleImpressum={toggleImpressum}/>
    {gameInfo.isLoading ?
      <div className="app-content loading"><CircularProgress /></div>
    : mobile ?
        <IntroductionPanel gameInfo={gameInfo} />
      :
        <Split minSize={0} snapOffset={200} sizes={[25, 50, 25]} className={`app-content level`}>
          <IntroductionPanel gameInfo={gameInfo} />
          <div className="world-image-container empty">
            {image &&
              // TODO: Temporary for testing
              <img className={worldId=="Proposition" ? "cover" : "contain"} src={path.join("data", gameId, image)} alt="" />
            }

          </div>
          <InventoryPanel levelInfo={inventory?.data} />
        </Split>
      }

  </>
}

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

function useLevelEditor(codeviewRef, initialCode, initialSelections, onDidChangeContent, onDidChangeSelection) {

  const connection = React.useContext(ConnectionContext)
  const gameId = React.useContext(GameIdContext)
  const {worldId, levelId} = useContext(WorldLevelIdContext)


  const [editor, setEditor] = useState<monaco.editor.IStandaloneCodeEditor|null>(null)
  const [infoProvider, setInfoProvider] = useState<null|InfoProvider>(null)
  const [infoviewApi, setInfoviewApi] = useState<null|InfoviewApi>(null)
  const [editorConnection, setEditorConnection] = useState<null|EditorConnection>(null)

  // Create Editor
  useEffect(() => {
    const editor = monaco.editor.create(codeviewRef.current!, {
      glyphMargin: true,
      quickSuggestions: false,
      lightbulb: {
        enabled: true
      },
      unicodeHighlight: {
          ambiguousCharacters: false,
      },
      automaticLayout: true,
      minimap: {
        enabled: false
      },
      lineNumbersMinChars: 3,
      'semanticHighlighting.enabled': true,
      theme: 'vs-code-theme-converted'
    })

    const infoProvider = new InfoProvider(connection.getLeanClient(gameId))

    const editorApi = infoProvider.getApi()

    const editorEvents: EditorEvents = {
        initialize: new EventEmitter(),
        gotServerNotification: new EventEmitter(),
        sentClientNotification: new EventEmitter(),
        serverRestarted: new EventEmitter(),
        serverStopped: new EventEmitter(),
        changedCursorLocation: new EventEmitter(),
        changedInfoviewConfig: new EventEmitter(),
        runTestScript: new EventEmitter(),
        requestedAction: new EventEmitter(),
    };

    // Challenge: write a type-correct fn from `Eventify<T>` to `T` without using `any`
    const infoviewApi: InfoviewApi = {
        initialize: async l => editorEvents.initialize.fire(l),
        gotServerNotification: async (method, params) => {
            editorEvents.gotServerNotification.fire([method, params]);
        },
        sentClientNotification: async (method, params) => {
            editorEvents.sentClientNotification.fire([method, params]);
        },
        serverRestarted: async r => editorEvents.serverRestarted.fire(r),
        serverStopped: async serverStoppedReason => {
            editorEvents.serverStopped.fire(serverStoppedReason)
        },
        changedCursorLocation: async loc => editorEvents.changedCursorLocation.fire(loc),
        changedInfoviewConfig: async conf => editorEvents.changedInfoviewConfig.fire(conf),
        requestedAction: async action => editorEvents.requestedAction.fire(action),
        // See https://rollupjs.org/guide/en/#avoiding-eval
        // eslint-disable-next-line @typescript-eslint/no-implied-eval
        runTestScript: async script => new Function(script)(),
        getInfoviewHtml: async () => document.body.innerHTML,
    };

    const ec = new EditorConnection(editorApi, editorEvents);
    setEditorConnection(ec)

    editorEvents.initialize.on((loc: Location) => ec.events.changedCursorLocation.fire(loc))

    setEditor(editor)
    setInfoProvider(infoProvider)
    setInfoviewApi(infoviewApi)

    return () => { infoProvider.dispose(); editor.dispose() }
  }, [])

  const {leanClient, leanClientStarted} = useLeanClient(gameId)
  const uriStr = `file:///${worldId}/${levelId}`
  const uri = monaco.Uri.parse(uriStr)

  // Create model when level changes
  useEffect(() => {
    if (editor && leanClientStarted) {

      let model = monaco.editor.getModel(uri)
      if (!model) {
        model = monaco.editor.createModel(initialCode, 'lean4', uri)
      }
      model.onDidChangeContent(() => onDidChangeContent(model.getValue()))
      editor.onDidChangeCursorSelection(() => onDidChangeSelection(editor.getSelections()))
      editor.setModel(model)
      if (initialSelections) {
        console.debug("Initial Selection: ", initialSelections)
        // BUG: Somehow I get an `invalid arguments` bug here
        // editor.setSelections(initialSelections)
      }

      return () => {
        editorConnection.api.sendClientNotification(uriStr, "textDocument/didClose", {textDocument: {uri: uriStr}})
        model.dispose();
      }
    }
  }, [editor, levelId, connection, leanClientStarted])


  useEffect(() => {
    if (editor && leanClientStarted) {

      let model = monaco.editor.getModel(uri)
      infoviewApi.serverRestarted(leanClient.initializeResult)

      infoProvider.openPreview(editor, infoviewApi)

      const taskGutter = new LeanTaskGutter(infoProvider.client, editor)
      const abbrevRewriter = new AbbreviationRewriter(new AbbreviationProvider(), model, editor)

      return () => { abbrevRewriter.dispose(); taskGutter.dispose(); }
    }
  }, [editor, connection, leanClientStarted])

  return {editor, infoProvider, editorConnection}
}
