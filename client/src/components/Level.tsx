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
import Inventory from './Inventory';
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
import { codeEdited, selectCode, progressSlice, selectCompleted } from '../state/progress';
import { useAppDispatch, useAppSelector } from '../hooks';
import { useStore } from 'react-redux';

import { EditorContext, ConfigContext, ProgressContext, VersionContext } from '../../../node_modules/lean4-infoview/src/infoview/contexts';
import { EditorConnection, EditorEvents } from '../../../node_modules/lean4-infoview/src/infoview/editorConnection';
import { EventEmitter } from '../../../node_modules/lean4-infoview/src/infoview/event';
import { Main } from './infoview/main'
import type { Location } from 'vscode-languageserver-protocol';

import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faHome, faArrowRight, faArrowLeft, faRotateLeft } from '@fortawesome/free-solid-svg-icons'

import { styled, useTheme, Theme, CSSObject } from '@mui/material/styles';
import Markdown from './Markdown';

import Split from 'react-split'

export const MonacoEditorContext = React.createContext<monaco.editor.IStandaloneCodeEditor>(null as any);

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

  const codeviewRef = useRef<HTMLDivElement>(null)
  const introductionPanelRef = useRef<HTMLDivElement>(null)

  const initialCode = useAppSelector(selectCode(worldId, levelId))

  const [commandLineMode, setCommandLineMode] = useState(true)
  const [commandLineInput, setCommandLineInput] = useState("")
  const [canUndo, setCanUndo] = useState(initialCode.trim() !== "")

  const theme = useTheme();

  useEffect(() => {
    // Scroll to top when loading a new level
    introductionPanelRef.current!.scrollTo(0,0)
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

  const connection = React.useContext(ConnectionContext)

  const gameInfo = useGetGameInfoQuery()

  useLoadWorldFiles(worldId)

  const level = useLoadLevelQuery({world: worldId, level: levelId})

  const dispatch = useAppDispatch()

  const onDidChangeContent = (code) => {
    dispatch(codeEdited({world: worldId, level: levelId, code}))

    setCanUndo(code.trim() !== "")
  }

  const completed = useAppSelector(selectCompleted(worldId, levelId))

  const {editor, infoProvider, editorConnection} =
    useLevelEditor(worldId, levelId, codeviewRef, initialCode, onDidChangeContent)

  return <>
    <div style={level.isLoading ? null : {display: "none"}} className="app-content loading"><CircularProgress /></div>
    <div style={level.isLoading ? {display: "none"} : null} className="app-bar">
      <div>
      <Button to={`/`}><FontAwesomeIcon icon={faHome} /></Button>
        <span className="app-bar-title">
          {gameInfo.data?.worlds.nodes[worldId].title && `World: ${gameInfo.data?.worlds.nodes[worldId].title}`}
        </span>
      </div>
      <div>
        <span className="app-bar-title">
          {levelId && `Level ${levelId}`}{level?.data?.title && `: ${level?.data?.title}`}
        </span>
        <Button disabled={levelId <= 1} inverted={true}
          to={`/world/${worldId}/level/${levelId - 1}`}
          ><FontAwesomeIcon icon={faArrowLeft} />&nbsp;Previous</Button>
        <Button disabled={levelId >= gameInfo.data?.worldSize[worldId]} inverted={true}
          to={`/world/${worldId}/level/${levelId + 1}`}
          >Next&nbsp;<FontAwesomeIcon icon={faArrowRight} /></Button>
      </div>

    </div>
    <Split minSize={0} snapOffset={200} sizes={[30, 45, 25]} className={`app-content level ${level.isLoading ? 'hidden' : ''}`}>
      <div className="side-panel">
        <div ref={introductionPanelRef} className="introduction-panel">
          <Markdown>{level?.data?.introduction}</Markdown>
        </div>
      </div>
      <div className="exercise-panel">
        <div className="exercise">
          {/* <h4>Aufgabe:</h4> */}
          <Markdown>{level?.data?.descrText}</Markdown>
          <div className={`statement ${commandLineMode ? 'hidden' : ''}`}><code>{level?.data?.descrFormat}</code></div>
          <div ref={codeviewRef} className={`codeview ${commandLineMode ? 'hidden' : ''}`}></div>
        </div>
        <div className="input-mode-switch">
          {commandLineMode && <button className="btn" onClick={handleUndo} disabled={!canUndo}><FontAwesomeIcon icon={faRotateLeft} /> Undo</button>}
          <FormGroup>
            <FormControlLabel control={<Switch onChange={(ev) => { setCommandLineMode(!commandLineMode) }} />} label="Editor mode" />
          </FormGroup>
        </div>

        <EditorContext.Provider value={editorConnection}>
          <MonacoEditorContext.Provider value={editor}>
            <InputModeContext.Provider value={{commandLineMode, setCommandLineMode, commandLineInput, setCommandLineInput}}>
              {editorConnection && <Main key={`${worldId}/${levelId}`} world={worldId} level={levelId} />}
            </InputModeContext.Provider>
          </MonacoEditorContext.Provider>
        </EditorContext.Provider>

        {completed && <div className="conclusion">
          <Markdown>{level?.data?.conclusion}</Markdown>
          {levelId >= gameInfo.data?.worldSize[worldId] ?
          <Button to={`/`}><FontAwesomeIcon icon={faHome} /></Button> :
          <Button to={`/world/${worldId}/level/${levelId + 1}`}>
            Next&nbsp;<FontAwesomeIcon icon={faArrowRight} /></Button>}

        </div>}
      </div>
      <div className="doc-panel">
        {!level.isLoading && <Inventory tactics={level?.data?.tactics} lemmas={level?.data?.lemmas} definitions={level?.data?.definitions} />}
      </div>
    </Split>
  </>
}

export default Level


function useLevelEditor(worldId: string, levelId: number, codeviewRef, initialCode, onDidChangeContent) {

  const connection = React.useContext(ConnectionContext)

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

    const infoProvider = new InfoProvider(connection.getLeanClient())

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

  const {leanClient, leanClientStarted} = useLeanClient()

  // Create model when level changes
  useEffect(() => {
    if (editor && leanClientStarted) {

      const uri = monaco.Uri.parse(`file:///${worldId}/${levelId}`)
      let model = monaco.editor.getModel(uri)
      if (!model) {
        model = monaco.editor.createModel(initialCode, 'lean4', uri)
      }
      model.onDidChangeContent(() => onDidChangeContent(model.getValue()))
      editor.setModel(model)
      editor.setPosition(model.getFullModelRange().getEndPosition())

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
  const gameInfo = useGetGameInfoQuery()
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
          const code = selectCode(worldId, levelId)(store.getState())
          models.push(monaco.editor.createModel(code, 'lean4', uri))
        }
      }
      return () => { for (let model of models) { model.dispose() } }
    }
  }, [gameInfo.data, worldId])
}
