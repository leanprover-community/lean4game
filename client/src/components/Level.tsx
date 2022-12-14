import * as React from 'react';
import { useEffect, useState, useRef } from 'react';
import '@fontsource/roboto/300.css';
import '@fontsource/roboto/400.css';
import '@fontsource/roboto/500.css';
import '@fontsource/roboto/700.css';
import ReactMarkdown from 'react-markdown';
import { MathJax } from "better-react-mathjax";
import { Link as RouterLink } from 'react-router-dom';
import { Box, Button, CircularProgress, FormControlLabel, FormGroup, Switch } from '@mui/material';
import Grid from '@mui/material/Unstable_Grid2';
import LeftPanel from './LeftPanel';
import { LeanTaskGutter } from 'lean4web/client/src/editor/taskgutter';
import { AbbreviationProvider } from 'lean4web/client/src/editor/abbreviation/AbbreviationProvider';
import { AbbreviationRewriter } from 'lean4web/client/src/editor/abbreviation/rewriter/AbbreviationRewriter';
import { InfoProvider } from 'lean4web/client/src/editor/infoview';
import 'lean4web/client/src/editor/infoview.css'
import { renderInfoview } from '@leanprover/infoview'
import * as monaco from 'monaco-editor/esm/vs/editor/editor.api.js'
import './level.css'
import { ConnectionContext } from '../connection';
import Infoview from './Infoview';
import { useParams } from 'react-router-dom';
import { useLoadLevelQuery } from '../state/api';
import { codeEdited, selectCode } from '../state/progress';
import { useAppDispatch } from '../hooks';
import { useSelector } from 'react-redux';



function Level() {

  const params = useParams();
  const levelId = parseInt(params.levelId)
  const worldId = params.worldId

  const [expertInfoview, setExpertInfoview] = useState(false)

  const codeviewRef = useRef<HTMLDivElement>(null)
  const infoviewRef = useRef<HTMLDivElement>(null)
  const messagePanelRef = useRef<HTMLDivElement>(null)

  useEffect(() => {
    // Scroll to top when loading a new level
    messagePanelRef.current!.scrollTo(0,0)
  }, [levelId])

  const connection = React.useContext(ConnectionContext)

  const level = useLoadLevelQuery({world: worldId, level: levelId})

  const dispatch = useAppDispatch()

  const onDidChangeContent = (code) => {
    dispatch(codeEdited({world: worldId, level: levelId, code}))
  }

  const initialCode = useSelector(selectCode(worldId, levelId))

  const {editor, infoProvider} =
    useLevelEditor(worldId, levelId, codeviewRef, infoviewRef, initialCode, onDidChangeContent)

  return <>
    <Box style={level.isLoading ? null : {display: "none"}} display="flex" alignItems="center" justifyContent="center" sx={{ height: "calc(100vh - 64px)" }}><CircularProgress /></Box>
    <Grid style={level.isLoading ? {display: "none"} : null} className="level" container sx={{ mt: 0, ml: 0, mr: 0 }} columnSpacing={{ xs: 1, sm: 2, md: 3 }}>
      <Grid xs={4} className="doc-panel">
        <LeftPanel spells={level?.data?.tactics} inventory={level?.data?.tactics} />
      </Grid>
      <Grid xs={9} sm={6} className="main-panel">
        <div ref={messagePanelRef} className="message-panel">
          <MathJax><ReactMarkdown>{level?.data?.introduction}</ReactMarkdown></MathJax>
        </div>
        <div className="exercise">
          <h4>Aufgabe:</h4>
          <MathJax><ReactMarkdown>{level?.data?.descrText}</ReactMarkdown></MathJax>
          <div className="statement"><code>{level?.data?.descrFormat}</code></div>
          <div ref={codeviewRef} className="codeview"></div>
        </div>
      </Grid>
      <Grid xs={3} className="info-panel">

        <Button disabled={levelId <= 1} component={RouterLink} to={`/world/${worldId}/level/${levelId - 1}`} sx={{ ml: 3, mt: 2, mb: 2 }} disableFocusRipple>Previous Level</Button>
        <Button disabled={false} component={RouterLink} to={`/world/${worldId}/level/${levelId + 1}`} sx={{ ml: 3, mt: 2, mb: 2 }} disableFocusRipple>Next Level</Button>

        <div style={{display: expertInfoview ? 'block' : 'none' }} ref={infoviewRef} className="infoview vscode-light"></div>
        <div style={{display: expertInfoview ? 'none' : 'block' }}>
          <Infoview leanClient={connection.getLeanClient()} editor={editor} editorApi={infoProvider?.getApi()} />
        </div>
        <FormGroup>
          <FormControlLabel onChange={() => { setExpertInfoview(!expertInfoview) }} control={<Switch />} label="Expert mode" />
        </FormGroup>
      </Grid>
    </Grid>
    </>
}

export default Level


function useLevelEditor(worldId: string, levelId: number, codeviewRef, infoviewRef, initialCode, onDidChangeContent) {

  const connection = React.useContext(ConnectionContext)

  const [editor, setEditor] = useState<monaco.editor.IStandaloneCodeEditor|null>(null)
  const [infoProvider, setInfoProvider] = useState<null|InfoProvider>(null)
  const [infoviewApi, setInfoviewApi] = useState(null)

  // Create Editor
  useEffect(() => {
    const editor = monaco.editor.create(codeviewRef.current!, {
      glyphMargin: true,
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
    const div: HTMLElement = infoviewRef.current!
    const infoviewApi = renderInfoview(infoProvider.getApi(), div)

    setEditor(editor)
    setInfoProvider(infoProvider)
    setInfoviewApi(infoviewApi)

    return () => { editor.setModel(null); infoProvider.dispose(); }
  }, [])

  // Create model when level changes
  useEffect(() => {
    connection.startLeanClient().then((leanClient) => {
      if (editor) {

        const uri = monaco.Uri.parse(`file:///${worldId}/${levelId}`)
        let model = monaco.editor.getModel(uri)
        if (!model) {
          model = monaco.editor.createModel(initialCode, 'lean4', uri)
          model.onDidChangeContent(() => onDidChangeContent(model.getValue()))
        }

        editor.setModel(model)
        infoviewApi.serverRestarted(leanClient.initializeResult)
        infoProvider.openPreview(editor, infoviewApi)
        new LeanTaskGutter(infoProvider.client, editor)

        new AbbreviationRewriter(new AbbreviationProvider(), model, editor)
      }
    })
    // TODO: Properly close the file to stop send "keepAlive" calls to the server
  }, [editor, levelId, connection])

  return {editor, infoProvider}
}
