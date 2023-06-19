import * as React from 'react';
import { useEffect, useState, useRef } from 'react';
import '@fontsource/roboto/300.css';
import '@fontsource/roboto/400.css';
import '@fontsource/roboto/500.css';
import '@fontsource/roboto/700.css';
import { InfoviewApi } from '@leanprover/infoview'
import { Link, useParams } from 'react-router-dom';
import { Box, CircularProgress, FormControlLabel, FormGroup, Switch, IconButton } from '@mui/material';
import MuiDrawer from '@mui/material/Drawer';
import Grid from '@mui/material/Unstable_Grid2';
import {Inventory, Documentation} from './Inventory';
import { LeanTaskGutter } from 'lean4web/client/src/editor/taskgutter';
import { AbbreviationProvider } from 'lean4web/client/src/editor/abbreviation/AbbreviationProvider';
import 'lean4web/client/src/editor/vscode.css';
import 'lean4web/client/src/editor/infoview.css';
import { AbbreviationRewriter } from 'lean4web/client/src/editor/abbreviation/rewriter/AbbreviationRewriter';
import { InfoProvider } from 'lean4web/client/src/editor/infoview';
import 'lean4web/client/src/editor/infoview.css'
import * as monaco from 'monaco-editor/esm/vs/editor/editor.api.js'
import './level.css'
import { Button } from './Button'
import { ConnectionContext, useLeanClient } from '../connection';
import { useGetGameInfoQuery, useLoadLevelQuery } from '../state/api';
import { changedSelection, codeEdited, selectCode, selectSelections, progressSlice, selectCompleted } from '../state/progress';
import { useAppDispatch, useAppSelector } from '../hooks';
import { useStore } from 'react-redux';

import { EditorContext, ConfigContext, ProgressContext, VersionContext } from '../../../node_modules/lean4-infoview/src/infoview/contexts';
import { EditorConnection, EditorEvents } from '../../../node_modules/lean4-infoview/src/infoview/editorConnection';
import { EventEmitter } from '../../../node_modules/lean4-infoview/src/infoview/event';
import { Main, EditorInterface } from './infoview/main'
import type { Location } from 'vscode-languageserver-protocol';

import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faHome, faArrowRight, faArrowLeft, faRotateLeft } from '@fortawesome/free-solid-svg-icons'

import { styled, useTheme, Theme, CSSObject } from '@mui/material/styles';
import Markdown from './Markdown';

import Split from 'react-split'
import { Alert } from '@mui/material';
import { GameIdContext } from '../App';

import { GameHint } from './infoview/rpcApi';
import { Hints } from './infoview/hints';

export const MonacoEditorContext = React.createContext<monaco.editor.IStandaloneCodeEditor>(null as any);

export const HintContext = React.createContext<{
  showHiddenHints : boolean,
  setShowHiddenHints: React.Dispatch<React.SetStateAction<boolean>>
  hints: Array<GameHint>,
  setHints: React.Dispatch<React.SetStateAction<Array<GameHint>>>
}>({
  showHiddenHints: true,
  setShowHiddenHints: () => {},
  hints: [],
  setHints: () => {},
});

export const InputModeContext = React.createContext<{
  commandLineMode: boolean,
  setCommandLineMode: React.Dispatch<React.SetStateAction<boolean>>,
  commandLineInput: string,
  setCommandLineInput: React.Dispatch<React.SetStateAction<string>>
}>({
  commandLineMode: true,
  setCommandLineMode: () => {},
  commandLineInput: "",
  setCommandLineInput: () => {},
});

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

// The mathematical formulation of the statement, supporting e.g. Latex
// It takes three forms, depending on the precence of name and description:
// - Theorem xyz: description
// - Theorem xyz
// - Exercises: description
function ExerciseStatement({data}) {
  return <div className="exercise-statement"><Markdown>
    {(data?.statementName ? `**Theorem** \`${data?.statementName}\`: ` : data?.descrText && "**Exercise**: ") + `${data?.descrText}` }
  </Markdown></div>
}

function ReducedInterface({worldId, levelId, editorConnection}) {
  return <div>
    {/* <button className="btn" onClick={handleUndo} disabled={!canUndo}><FontAwesomeIcon icon={faRotateLeft} /> Undo</button> */}
    {editorConnection && <Main key={`${worldId}/${levelId}`} world={worldId} level={levelId} />}
  </div>
}

function PlayableLevel({worldId, levelId}) {
  const codeviewRef = useRef<HTMLDivElement>(null)
  const chatPanelRef = useRef<HTMLDivElement>(null)

  const gameId = React.useContext(GameIdContext)
  const initialCode = useAppSelector(selectCode(gameId, worldId, levelId))
  const initialSelections = useAppSelector(selectSelections(gameId, worldId, levelId))

  const [commandLineMode, setCommandLineMode] = useState(true)
  const [commandLineInput, setCommandLineInput] = useState("")
  const [canUndo, setCanUndo] = useState(initialCode.trim() !== "")

  // The array of all shown hints. This excludes introduction and conclusion
  // TODO: Not used yet
  const [hints, setHints] = useState(Array<GameHint>)
  const [showHiddenHints, setShowHiddenHints] = useState(false)

  const theme = useTheme();


  useEffect(() => {
    // Scroll to top when loading a new level
    // TODO: Thats the wrong behaviour probably
    chatPanelRef.current!.scrollTo(0,0)
    // Reset command line input when loading a new level
    setCommandLineInput("")
  }, [levelId])

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

  const levelTitle = <>{levelId && `Level ${levelId}`}{level?.data?.title && `: ${level?.data?.title}`}</>

  return <>
    <div style={level.isLoading ? null : {display: "none"}} className="app-content loading"><CircularProgress /></div>
    <InputModeContext.Provider value={{commandLineMode, setCommandLineMode, commandLineInput, setCommandLineInput}}>
    <HintContext.Provider value={{showHiddenHints, setShowHiddenHints, hints, setHints}}>
      <LevelAppBar isLoading={level.isLoading} levelTitle={levelTitle} worldId={worldId} levelId={levelId} />
      <Split minSize={0} snapOffset={200} sizes={[25, 50, 25]} className={`app-content level ${level.isLoading ? 'hidden' : ''}`}>
        <div ref={chatPanelRef} className="chat-panel">
          <div className="chat">
            {level?.data?.introduction &&
              <div className="message info">
                <Markdown>{level?.data?.introduction}</Markdown>
              </div>
            }
                {/* {openHints.map(hint => <Hint hint={hint} />)}
      {hiddenHints.length > 0 &&
          <FormControlLabel
            control={<Switch checked={showHints} onChange={() => setShowHints((prev) => !prev)} />}
            label="I need help!"
          />}
      {showHints && hiddenHints.map(hint => <Hint hint={hint} />)} */}
            {hints.map(hint =>
              <div className="message info"><Markdown>{hint.text}</Markdown></div>)
            }
            {completed &&
              <>
                <div className="message info">
                  Level completed! 🎉
                </div>
                {level?.data?.conclusion?.trim() &&
                  <div className="message info">
                    <Markdown>{level?.data?.conclusion}</Markdown>
                  </div>
                }
                {levelId >= gameInfo.data?.worldSize[worldId] ?
                <Button to={`/${gameId}`}><FontAwesomeIcon icon={faHome} /></Button> :
                <Button to={`/${gameId}/world/${worldId}/level/${levelId + 1}`}>
                  Next&nbsp;<FontAwesomeIcon icon={faArrowRight} /></Button>}
              </>
            }

            {/* { hints.map(hint => <div className="message info"><Markdown>{hint.text}</Markdown></div>) } */}
            <Hints hints={hints} showHidden={showHiddenHints}/>
            {/* TODO: Remove this debugging message: */}
            {showHiddenHints && <p>Hidden Hints are displayed</p>}
          </div>
          <div className="toggle-hidden-hints">
            <FormControlLabel
              control={<Switch checked={showHiddenHints} onChange={() => setShowHiddenHints((prev) => !prev)} />}
              label="Show more help!"
            />
          </div>
        </div>
        <div className="exercise-panel">
          <EditorContext.Provider value={editorConnection}>
          <MonacoEditorContext.Provider value={editor}>
          <ExerciseStatement data={level?.data} />
          <div className="exercise">
            {/* We need the editor to be hidden because the command line edits its content */}
            <EditorInterface data={level?.data} codeviewRef={codeviewRef} hidden={commandLineMode}
              worldId={worldId} levelId={levelId} editorConnection={editorConnection}/>
            {commandLineMode && <ReducedInterface worldId={worldId} levelId={levelId} editorConnection={editorConnection}/>}
            {/* <div className={`statement ${commandLineMode ? 'hidden' : ''}`}><code>{level?.data?.descrFormat}</code></div> */}
            {/* <div ref={codeviewRef} className={`codeview ${commandLineMode ? 'hidden' : ''}`}></div> */}
          </div>
          {/* <div className="input-mode-switch">
            {commandLineMode && <button className="btn" onClick={handleUndo} disabled={!canUndo}><FontAwesomeIcon icon={faRotateLeft} /> Undo</button>}
          </div> */}
                {/* {editorConnection && <Main key={`${worldId}/${levelId}`} world={worldId} level={levelId} />} */}
          </MonacoEditorContext.Provider>
          </EditorContext.Provider>
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
    </HintContext.Provider>
    </InputModeContext.Provider>
  </>
}

export default Level

function Introduction({worldId}) {
  const gameId = React.useContext(GameIdContext)
  const gameInfo = useGetGameInfoQuery({game: gameId})

  return <>
    <div style={gameInfo.isLoading ? null : {display: "none"}} className="app-content loading"><CircularProgress /></div>
    <LevelAppBar isLoading={gameInfo.isLoading} levelTitle="Einführung" worldId={worldId} levelId={0} />
    <div style={gameInfo.isLoading ? {display: "none"} : null} className="exercise-panel">
      <div className="introduction-panel">
        <div className="message info">
            <Markdown>
              {gameInfo.data?.worlds.nodes[worldId].introduction}
            </Markdown>
          </div>
      </div>
      <div className="conclusion">
        {0 == gameInfo.data?.worldSize[worldId] ?
        <Button to={`/${gameId}`}><FontAwesomeIcon icon={faHome} /></Button> :
        <Button to={`/${gameId}/world/${worldId}/level/1`}>
          Start&nbsp;<FontAwesomeIcon icon={faArrowRight} />
        </Button>}
      </div>
    </div>
  </>
}

function LevelAppBar({isLoading, levelId, worldId, levelTitle}) {
  const gameId = React.useContext(GameIdContext)
  const gameInfo = useGetGameInfoQuery({game: gameId})

  const { commandLineMode, setCommandLineMode } = React.useContext(InputModeContext)

  return <div className="app-bar" style={isLoading ? {display: "none"} : null} >
    <div>
      <Button to={`/${gameId}`}><FontAwesomeIcon icon={faHome} /></Button>
        <span className="app-bar-title">
          {gameInfo.data?.worlds.nodes[worldId].title && `World: ${gameInfo.data?.worlds.nodes[worldId].title}`}
        </span>
      </div>
    <div>
      <span className="app-bar-title">
        {levelTitle}
      </span>
        <Button disabled={levelId <= 0} inverted={true} to=""
          onClick={(ev) => { setCommandLineMode(!commandLineMode) }}>Editor</Button>
      <Button disabled={levelId <= 0} inverted={true}
        to={`/${gameId}/world/${worldId}/level/${levelId - 1}`}
        ><FontAwesomeIcon icon={faArrowLeft} />&nbsp;Previous</Button>
      <Button disabled={levelId >= gameInfo.data?.worldSize[worldId]} inverted={true}
        to={`/${gameId}/world/${worldId}/level/${levelId + 1}`}
        >Next&nbsp;<FontAwesomeIcon icon={faArrowRight} /></Button>
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

  // Create model when level changes
  useEffect(() => {
    if (editor && leanClientStarted) {

      const uri = monaco.Uri.parse(`file:///${worldId}/${levelId}`)
      let model = monaco.editor.getModel(uri)
      if (!model) {
        model = monaco.editor.createModel(initialCode, 'lean4', uri)
      }
      model.onDidChangeContent(() => onDidChangeContent(model.getValue()))
      editor.onDidChangeCursorSelection(() => onDidChangeSelection(editor.getSelections()))
      editor.setModel(model)
      if (initialSelections) {
        editor.setSelections(initialSelections)
      }

      infoviewApi.serverRestarted(leanClient.initializeResult)
      infoProvider.openPreview(editor, infoviewApi)

      const taskGutter = new LeanTaskGutter(infoProvider.client, editor)
      const abbrevRewriter = new AbbreviationRewriter(new AbbreviationProvider(), model, editor)

      return () => { abbrevRewriter.dispose(); taskGutter.dispose(); }
    }
  }, [editor, levelId, connection, leanClientStarted])

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
