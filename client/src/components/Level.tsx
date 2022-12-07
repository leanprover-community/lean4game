import * as React from 'react';
import { useEffect, useState, useRef } from 'react';
import '@fontsource/roboto/300.css';
import '@fontsource/roboto/400.css';
import '@fontsource/roboto/500.css';
import '@fontsource/roboto/700.css';
import ReactMarkdown from 'react-markdown';
import { MathJax } from "better-react-mathjax";
import { Link as RouterLink } from 'react-router-dom';


import { Button, FormControlLabel, FormGroup, Switch } from '@mui/material';
import Grid from '@mui/material/Unstable_Grid2';

import LeftPanel from './LeftPanel';
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
import { MonacoServices } from 'monaco-languageclient';



function Level() {

  const params = useParams();
  const levelId = parseInt(params.levelId)
  const worldId = params.worldId

  const [tacticDocs, setTacticDocs] = useState([])
  const [lemmaDocs, setLemmaDocs] = useState([])
  const [editor, setEditor] = useState<monaco.editor.IStandaloneCodeEditor|null>(null)
  const [infoProvider, setInfoProvider] = useState<null|InfoProvider>(null)
  const [infoviewApi, setInfoviewApi] = useState(null)
  const [expertInfoview, setExpertInfoview] = useState(false)


  const [leanData, setLeanData] = useState({goals: []})
  const [history, setHistory] = useState([])
  const [lastTactic, setLastTactic] = useState("")
  const [introduction, setIntroduction] = useState("")
  const [errors, setErrors] = useState([])
  const codeviewRef = useRef<HTMLDivElement>(null)
  const infoviewRef = useRef<HTMLDivElement>(null)
  const messagePanelRef = useRef<HTMLDivElement>(null)

  const [ready, setReady] = useState(false)

  const [message, setMessage] = useState("")
  const [messageOpen, setMessageOpen] = useState(false)


  const [completed, setCompleted] = useState(false)

  const processResponse = (res:any) => {
    setLeanData(res);
    // setErrors(res.errors);
    // if (res.message !== "" && res.errors?.length === 0) {
    //   setMessage(res.message)
    //   setMessageOpen(true)
    // }
    // if (res.goals?.length === 0 && res.errors?.length === 0) {
    //   setCompleted(true)
    // }
  }

  useEffect(() => {
    // Scroll to top when loading a new level
    messagePanelRef.current!.scrollTo(0,0)
  }, [levelId])

  const connection = React.useContext(ConnectionContext)

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

    return () => { editor.dispose() }
  }, [])

  const uri = `file:///${worldId}/${levelId}`

  // The next function will be called when the level changes
  useEffect(() => {
    connection.whenLeanClientStarted((leanClient) => {
      if (editor) {

        const model = monaco.editor.createModel('', 'lean4', monaco.Uri.parse(uri))

        editor.setModel(model)
        infoviewApi.serverRestarted(leanClient.initializeResult)
        infoProvider.openPreview(editor, infoviewApi)
        setReady(true)

        new AbbreviationRewriter(new AbbreviationProvider(), model, editor)


        leanClient.sendRequest("loadLevel", {world: worldId, level: levelId}).then((res) => {
          // setLevelTitle("Level " + res["index"] + ": " + res["title"])
          // setIndex(parseInt(res["index"]))
          setTacticDocs(res["tactics"])
          setLemmaDocs(res["lemmas"])
          setIntroduction(res["introduction"])
          processResponse(res)
        });

        return () => { model.dispose(); setReady(false) }
      }
    })

  }, [editor, levelId, connection])

  function loadLevel(index) {
    setCompleted(false)
    setHistory([])
    // setCurLevel(index)
  }

  return (
    <Grid className="level" container sx={{ mt: 3, ml: 1, mr: 1 }} columnSpacing={{ xs: 1, sm: 2, md: 3 }}>
      <Grid xs={4} className="doc-panel">
        <LeftPanel spells={tacticDocs} inventory={lemmaDocs} />
      </Grid>
      <Grid xs={4} className="main-panel">
        <div ref={messagePanelRef} className="message-panel">
          <MathJax><ReactMarkdown>{introduction}</ReactMarkdown></MathJax>
        </div>
        <div ref={codeviewRef} className="codeview">
          {/* <InputZone index={index} history={history} messageOpen={messageOpen} setMessageOpen={setMessageOpen} completed={completed} sendTactic={sendTactic} nbLevels={nbLevels} loadNextLevel={loadNextLevel}
            errors={errors} lastTactic={lastTactic} undo={undo} finishGame={finishGame} /> */}
          {/* <Message isOpen={messageOpen} content={message} close={closeMessage} /> */}
        </div>
      </Grid>
      <Grid xs={4} className="info-panel">

        <Button disabled={levelId <= 1} component={RouterLink} to={`/level/${levelId - 1}`} sx={{ ml: 3, mt: 2, mb: 2 }} disableFocusRipple>Previous Level</Button>
        <Button disabled={false} component={RouterLink} to={`/level/${levelId + 1}`} sx={{ ml: 3, mt: 2, mb: 2 }} disableFocusRipple>Next Level</Button>

        <div style={{display: expertInfoview ? 'block' : 'none' }} ref={infoviewRef} className="infoview vscode-light"></div>
        <div style={{display: expertInfoview ? 'none' : 'block' }}>
          <Infoview leanClient={connection.getLeanClient()} editor={editor} editorApi={infoProvider?.getApi()} />
        </div>
        <FormGroup>
          <FormControlLabel onChange={() => { setExpertInfoview(!expertInfoview) }} control={<Switch />} label="Expert mode" />
        </FormGroup>
      </Grid>
    </Grid>
  )
}

export default Level
