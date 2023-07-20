import * as React from 'react';
import { useEffect, useState, useRef } from 'react';
import Split from 'react-split'
import { Alert } from '@mui/material';
import '@fontsource/roboto/300.css';
import '@fontsource/roboto/400.css';
import '@fontsource/roboto/500.css';
import '@fontsource/roboto/700.css';
import { InfoviewApi, defaultInfoviewConfig } from '@leanprover/infoview'
import { Link, useParams } from 'react-router-dom';
import { Box, CircularProgress, FormControlLabel, FormGroup, Switch, IconButton } from '@mui/material';
import MuiDrawer from '@mui/material/Drawer';
import Grid from '@mui/material/Unstable_Grid2';
import { LeanTaskGutter } from 'lean4web/client/src/editor/taskgutter';
import { AbbreviationProvider } from 'lean4web/client/src/editor/abbreviation/AbbreviationProvider';
import 'lean4web/client/src/editor/vscode.css';
import 'lean4web/client/src/editor/infoview.css';
import { AbbreviationRewriter } from 'lean4web/client/src/editor/abbreviation/rewriter/AbbreviationRewriter';
import { InfoProvider } from 'lean4web/client/src/editor/infoview';
import 'lean4web/client/src/editor/infoview.css'
import * as monaco from 'monaco-editor/esm/vs/editor/editor.api.js'
import './level.css'
import { useStore } from 'react-redux';
import { EditorContext, ConfigContext, ProgressContext, VersionContext } from '../../../node_modules/lean4-infoview/src/infoview/contexts';
import { EditorConnection, EditorEvents } from '../../../node_modules/lean4-infoview/src/infoview/editorConnection';
import { EventEmitter } from '../../../node_modules/lean4-infoview/src/infoview/event';
import type { Location } from 'vscode-languageserver-protocol';
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faBars, faHome, faCircleInfo, faArrowRight, faArrowLeft, faShield, faRotateLeft } from '@fortawesome/free-solid-svg-icons'
import { styled, useTheme, Theme, CSSObject } from '@mui/material/styles';

import { GameIdContext } from '../app';
import { ConnectionContext, useLeanClient } from '../connection';
import { useAppDispatch, useAppSelector } from '../hooks';
import { Button } from './button'
import Markdown from './markdown';
import {Inventory, Documentation} from './inventory';
import { useGetGameInfoQuery, useLoadLevelQuery } from '../state/api';
import { changedSelection, codeEdited, selectCode, selectSelections, progressSlice, selectCompleted, helpEdited, selectHelp } from '../state/progress';
import { DualEditor } from './infoview/main'
import { DeletedHint, DeletedHints, Hints } from './hints';
import { DeletedChatContext, InputModeContext, MonacoEditorContext, ProofContext, ProofStep, SelectionContext } from './infoview/context';
import { hasInteractiveErrors } from './infoview/command_line';
import { GameHint } from './infoview/rpc_api';
import { Impressum } from './privacy_policy';

function Level() {

  const params = useParams();
  const levelId = parseInt(params.levelId)
  const worldId = params.worldId

  useLoadWorldFiles(worldId)

  if (levelId == 0) {
    return <Introduction worldId={worldId} />
  } else {
    return <PlayableLevel worldId={worldId} levelId={levelId} />
  }
}

function PlayableLevel({worldId, levelId}) {
  const codeviewRef = useRef<HTMLDivElement>(null)

  const chatRef = useRef<HTMLDivElement>(null)

  const gameId = React.useContext(GameIdContext)

  // The state variables for the `ProofContext`
  const [proof, setProof] = useState<Array<ProofStep>>([])

  // When deleting the proof, we want to keep to old messages around until
  // a new proof has been entered. e.g. to consult messages coming from dead ends
  const [deletedChat, setDeletedChat] = useState<Array<GameHint>>([])

  const store = useStore()

  // A set of row numbers where help is displayed
  const [showHelp, setShowHelp] = useState<Set<number>>(new Set())

  const initialCode = useAppSelector(selectCode(gameId, worldId, levelId))
  const initialSelections = useAppSelector(selectSelections(gameId, worldId, levelId))

  const [commandLineMode, setCommandLineMode] = useState(true)
  const [commandLineInput, setCommandLineInput] = useState("")
  const [canUndo, setCanUndo] = useState(initialCode.trim() !== "")

  const [selectedStep, setSelectedStep] = useState<number>()

  const theme = useTheme();

  const [impressum, setImpressum] = React.useState(false)

  function closeImpressum() {
    setImpressum(false)
  }

  function toggleImpressum() {
    setImpressum(!impressum)
  }

  useEffect(() => {
    // // Scroll to top when loading a new level
    // // TODO: Thats the wrong behaviour probably
    // chatRef.current!.scrollTo(0,0)

    // TODO: That's a problem if the saved proof contains an error
    // Reset command line input when loading a new level
    setCommandLineInput("")

    // Load the selected help steps from the store
    setShowHelp(new Set(selectHelp(gameId, worldId, levelId)(store.getState())))
  }, [gameId, worldId, levelId])

  useEffect(() => {
    // TODO: For some reason this is always called twice
    console.debug('scroll chat')
    chatRef.current!.lastElementChild?.scrollIntoView() //scrollTo(0,0)
  }, [proof, showHelp])

  React.useEffect(() => {
    if (!commandLineMode) {
      // Delete last input attempt from command line
      editor.executeEdits("command-line", [{
        range: editor.getSelection(),
        text: "",
        forceMoveMarkers: false
      }]);
      editor.focus()
    }
  }, [commandLineMode])

  // Scroll to element if selection changes
  React.useEffect(() => {
    if (typeof selectedStep !== 'undefined') {
      Array.from(chatRef.current?.getElementsByClassName(`step-${selectedStep}`)).map((elem) => {
        elem.scrollIntoView({block: "center"})
      })
    }
  }, [selectedStep])

  React.useEffect(() => {
    // Forget whether hidden hints are displayed for steps that don't exist yet
    if (proof.length) {
      console.debug(Array.from(showHelp))
      setShowHelp(new Set(Array.from(showHelp).filter(i => (i < proof.length))))
    }
  }, [proof])

  /** Unused. Was implementing an undo button, which has been replaced by `deleteProof` inside
   * `CommandLineInterface`.
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

  const gameInfo = useGetGameInfoQuery({game: gameId})
  const level = useLoadLevelQuery({game: gameId, world: worldId, level: levelId})

  const dispatch = useAppDispatch()

  const onDidChangeContent = (code) => {
    dispatch(codeEdited({game: gameId, world: worldId, level: levelId, code}))

    setCanUndo(code.trim() !== "")
  }

  // save showed help in store
  useEffect(() => {
    if (proof.length) {
      console.debug(`showHelp:\n ${showHelp}`)
      dispatch(helpEdited({game: gameId, world: worldId, level: levelId, help: Array.from(showHelp)}))
    }
  }, [showHelp])

  const onDidChangeSelection = (monacoSelections) => {
    const selections = monacoSelections.map(
      ({selectionStartLineNumber, selectionStartColumn, positionLineNumber, positionColumn}) =>
      {return {selectionStartLineNumber, selectionStartColumn, positionLineNumber, positionColumn}})
    dispatch(changedSelection({game: gameId, world: worldId, level: levelId, selections}))
  }

  const completed = useAppSelector(selectCompleted(gameId, worldId, levelId))

  const {editor, infoProvider, editorConnection} =
    useLevelEditor(worldId, levelId, codeviewRef, initialCode, initialSelections, onDidChangeContent, onDidChangeSelection)

  // Effect when command line mode gets enabled
  useEffect(() => {
    if (editor && commandLineMode) {
      let endPos = editor.getModel().getFullModelRange().getEndPosition()
      if (editor.getModel().getLineContent(endPos.lineNumber).trim() !== "") {
        editor.executeEdits("command-line", [{
          range: monaco.Selection.fromPositions(endPos, endPos),
          text: "\n",
          forceMoveMarkers: true
        }]);
      }
      endPos = editor.getModel().getFullModelRange().getEndPosition()
      let currPos = editor.getPosition()
      if (currPos.column != 1 || (currPos.lineNumber != endPos.lineNumber && currPos.lineNumber != endPos.lineNumber - 1)) {
        // This is not a position that would naturally occur from CommandLine, reset:
        editor.setSelection(monaco.Selection.fromPositions(endPos, endPos))
      }
    }
  }, [editor, commandLineMode])

  // When clicking on an inventory item, the inventory is overlayed by the item's doc.
  // If this state is set to a pair `(name, type)` then the according doc will be open.
  const [inventoryDoc, setInventoryDoc] = useState<{name: string, type: string}>(null)

  // Open the doc of the clicked inventory item
  function openInventoryDoc(name, type) {
    setInventoryDoc({name, type})
  }

  // Set `inventoryDoc` to `null` to close the doc
  const closeInventoryDoc = () => setInventoryDoc(null);

  const levelTitle = <>
    {levelId && `Level ${levelId} / ${gameInfo.data?.worldSize[worldId]}`}{level?.data?.title && `: ${level?.data?.title}`}</>

  // TODO: with the new design, there is no difference between the introduction and
  // a hint at the beginning of the proof...

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

  // If the last step has errors, we want to treat it as if it is part of the second-to-last step
  let k = proof.length - 1
  let withErr = hasInteractiveErrors(proof[k]?.errors) ? 1 : 0

  return <>
    <div style={level.isLoading ? null : {display: "none"}} className="app-content loading"><CircularProgress /></div>
    <DeletedChatContext.Provider value={{deletedChat, setDeletedChat, showHelp, setShowHelp}}>
    <SelectionContext.Provider value={{selectedStep, setSelectedStep}}>
    <InputModeContext.Provider value={{commandLineMode, setCommandLineMode, commandLineInput, setCommandLineInput}}>
    <ProofContext.Provider value={{proof, setProof}}>
      <LevelAppBar isLoading={level.isLoading} levelTitle={`Level ${levelId} / ${gameInfo.data?.worldSize[worldId]}` + (level?.data?.title && ` : ${level?.data?.title}`)} worldId={worldId} levelId={levelId} toggleImpressum={toggleImpressum}/>
      <Split minSize={0} snapOffset={200} sizes={[25, 50, 25]} className={`app-content level ${level.isLoading ? 'hidden' : ''}`}>
        <div className="chat-panel">
          <div ref={chatRef} className="chat">
            {level?.data?.introduction &&
              <div className={`message information step-0${selectedStep === 0 ? ' selected' : ''}`} onClick={toggleSelection(0)}>
                <Markdown>{level?.data?.introduction}</Markdown>
              </div>
            }
            {proof.map((step, i) => {
              // It the last step has errors, it will have the same hints
              // as the second-to-last step. Therefore we should not display them.
              if (!(i == proof.length - 1 && withErr)) {
                // TODO: Should not use index as key.
                return <Hints key={`hints-${i}`}
                  hints={step.hints} showHidden={showHelp.has(i)} step={i}
                  selected={selectedStep} toggleSelection={toggleSelection(i)}/>
              }
            })}
            <DeletedHints hints={deletedChat}/>
            {completed &&
              <>
                <div className={`message information step-${k}${selectedStep == k ? ' selected' : ''}`} onClick={toggleSelection(k)}>
                  Level completed! 🎉
                </div>
                {level?.data?.conclusion?.trim() &&
                  <div className={`message information step-${k}${selectedStep == k ? ' selected' : ''}`} onClick={toggleSelection(k)}>
                    <Markdown>{level?.data?.conclusion}</Markdown>
                  </div>
                }
                {levelId >= gameInfo.data?.worldSize[worldId] ?
                <Button to={`/${gameId}`}><FontAwesomeIcon icon={faHome} /> Leave World</Button> :
                <Button to={`/${gameId}/world/${worldId}/level/${levelId + 1}`}>
                  Next&nbsp;<FontAwesomeIcon icon={faArrowRight} /></Button>}
              </>
            }
          </div>
          <div className="toggle-hidden-hints">
            <FormControlLabel
              control={<Switch checked={showHelp.has(k - withErr)} onChange={(ev) => {
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
              }} />}
              label="Show more help!"
            />
          </div>
        </div>
        <div className="exercise-panel">
          <EditorContext.Provider value={editorConnection}>
            <MonacoEditorContext.Provider value={editor}>
              <div className="exercise">
                <DualEditor level={level} codeviewRef={codeviewRef} levelId={levelId} worldId={worldId} />
              </div>
            </MonacoEditorContext.Provider>
          </EditorContext.Provider>
          {impressum ? <Impressum handleClose={closeImpressum} /> : null}
        </div>
        <div className="inventory-panel">
          {!level.isLoading &&
            <>{inventoryDoc ?
              <Documentation name={inventoryDoc.name} type={inventoryDoc.type} handleClose={closeInventoryDoc}/>
              :
              <Inventory levelInfo={level?.data} openDoc={openInventoryDoc} />
            }</>
          }
        </div>
      </Split>
    </ProofContext.Provider>
    </InputModeContext.Provider>
    </SelectionContext.Provider>
    </DeletedChatContext.Provider>
  </>
}

export default Level

/** The site with the introduction text of a world */
function Introduction({worldId}) {
  const gameId = React.useContext(GameIdContext)
  const gameInfo = useGetGameInfoQuery({game: gameId})

  const [impressum, setImpressum] = React.useState(false)

  const closeImpressum = () => {
    setImpressum(false)
  }

  const toggleImpressum = () => {
    setImpressum(!impressum)
  }

  return <>
    <div style={gameInfo.isLoading ? null : {display: "none"}} className="app-content loading"><CircularProgress /></div>
    <LevelAppBar isLoading={gameInfo.isLoading} levelTitle="Introduction" worldId={worldId} levelId={0} toggleImpressum={toggleImpressum}/>
    <div style={gameInfo.isLoading ? {display: "none"} : null} className="introduction-panel">
      <div className="content-wrapper">
        <Markdown>
          {gameInfo.data?.worlds.nodes[worldId].introduction}
        </Markdown>
        {impressum ? <Impressum handleClose={closeImpressum} /> : null}
      </div>
      {gameInfo.data?.worldSize[worldId] == 0 ?
        <Button to={`/${gameId}`}><FontAwesomeIcon icon={faHome} /></Button> :
        <Button to={`/${gameId}/world/${worldId}/level/1`}>
          Start&nbsp;<FontAwesomeIcon icon={faArrowRight} />
        </Button>
      }
    </div>
  </>
}

/** The top-navigation bar */
function LevelAppBar({isLoading, levelId, worldId, levelTitle, toggleImpressum}) {
  const gameId = React.useContext(GameIdContext)
  const gameInfo = useGetGameInfoQuery({game: gameId})

  const { commandLineMode, setCommandLineMode } = React.useContext(InputModeContext)

  return <div className="app-bar" style={isLoading ? {display: "none"} : null} >
    <div>
      <span className="app-bar-title">
        {gameInfo.data?.worlds.nodes[worldId].title && `World: ${gameInfo.data?.worlds.nodes[worldId].title}`}
      </span>
    </div>
    <div>
      <span className="app-bar-title">
        {levelTitle}
      </span>
        {levelId > 0 && <>
          <Button disabled={levelId <= 0} inverted="true" to=""
              onClick={(ev) => { setCommandLineMode(!commandLineMode) }}
              title="toggle Editor mode">
            Editor
          </Button>
          <Button disabled={levelId <= 0} inverted="true"
              to={`/${gameId}/world/${worldId}/level/${levelId - 1}`}
              title="previous level">
            <FontAwesomeIcon icon={faArrowLeft} />&nbsp;Previous
          </Button>
        </>}
        {levelId < gameInfo.data?.worldSize[worldId] &&
          <Button inverted="true" to={`/${gameId}/world/${worldId}/level/${levelId + 1}`} title="next level">
            Next&nbsp;<FontAwesomeIcon icon={faArrowRight} />
          </Button>
        }

        <Button title="information, Impressum, privacy policy" inverted="true" to="" onClick={toggleImpressum}>
          <FontAwesomeIcon icon={faCircleInfo} /> Info &amp; Impressum
        </Button>
        <Button to={`/${gameId}`} inverted="true" title="back to world selection">
          <FontAwesomeIcon icon={faHome} /> Home
        </Button>
        <Button to="" inverted="true">
          <FontAwesomeIcon icon={faBars} />
        </Button>
    </div>

  </div>
}

function useLevelEditor(worldId: string, levelId: number, codeviewRef, initialCode, initialSelections, onDidChangeContent, onDidChangeSelection) {

  const connection = React.useContext(ConnectionContext)
  const gameId = React.useContext(GameIdContext)

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

  const uri = monaco.Uri.parse(`file:///${worldId}/${levelId}`)

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

/** Open all files in this world on the server so that they will load faster when accessed */
function useLoadWorldFiles(worldId) {
  const gameId = React.useContext(GameIdContext)
  const gameInfo = useGetGameInfoQuery({game: gameId})
  const store = useStore()

  useEffect(() => {
    if (gameInfo.data) {
      const models = []
      for (let levelId = 1; levelId <= gameInfo.data.worldSize[worldId]; levelId++) {
        const uri = monaco.Uri.parse(`file:///${worldId}/${levelId}`)
        let model = monaco.editor.getModel(uri)
        if (model) {
          models.push(model)
        } else {
          const code = selectCode(gameId, worldId, levelId)(store.getState())
          models.push(monaco.editor.createModel(code, 'lean4', uri))
        }
      }
      return () => { for (let model of models) { model.dispose() } }
    }
  }, [gameInfo.data, worldId])
}
