import * as React from 'react';
import { useEffect, useState, useRef } from 'react';
import '@fontsource/roboto/300.css';
import '@fontsource/roboto/400.css';
import '@fontsource/roboto/500.css';
import '@fontsource/roboto/700.css';
import ReactMarkdown from 'react-markdown';
import { MathJax } from "better-react-mathjax";

import { Button } from '@mui/material';
import Grid from '@mui/material/Unstable_Grid2';

import LeftPanel from './LeftPanel';
import InputZone from './InputZone';
import Message from './Message';
import TacticState from './TacticState';
import { LeanClient } from 'lean4web/client/src/editor/leanclient';
import { AbbreviationProvider } from 'lean4web/client/src/editor/abbreviation/AbbreviationProvider';
import { AbbreviationRewriter } from 'lean4web/client/src/editor/abbreviation/rewriter/AbbreviationRewriter';
import { InfoProvider } from 'lean4web/client/src/editor/infoview';
import 'lean4web/client/src/editor/infoview.css'
import { renderInfoview } from '@leanprover/infoview'
import * as monaco from 'monaco-editor/esm/vs/editor/editor.api.js'
import './level.css'
import { ConnectionContext } from '../connection';

interface LevelProps {
  nbLevels: any;
  level: any;
  setCurLevel: any;
  setLevelTitle: any;
  setFinished: any
}

function Level({ nbLevels, level, setCurLevel, setLevelTitle, setFinished }: LevelProps) {
  const [index, setIndex] = useState(level) // Level number
  const [tacticDocs, setTacticDocs] = useState([])
  const [lemmaDocs, setLemmaDocs] = useState([])
  const [editor, setEditor] = useState(null)
  const [infoProvider, setInfoProvider] = useState(null)
  const [infoviewApi, setInfoviewApi] = useState(null)

  const [leanData, setLeanData] = useState({goals: []})
  const [history, setHistory] = useState([])
  const [lastTactic, setLastTactic] = useState("")
  const [introduction, setIntroduction] = useState("")
  const [errors, setErrors] = useState([])
  const codeviewRef = useRef<HTMLDivElement>(null)
  const infoviewRef = useRef<HTMLDivElement>(null)
  const messagePanelRef = useRef<HTMLDivElement>(null)

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
  }, [level])

  const leanClient = React.useContext(ConnectionContext)

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

    const infoProvider = new InfoProvider(leanClient)
    const div: HTMLElement = infoviewRef.current!
    const infoviewApi = renderInfoview(infoProvider.getApi(), div)

    setEditor(editor)
    setInfoProvider(infoProvider)
    setInfoviewApi(infoviewApi)

    return () => { editor.dispose() }
  }, [])

  // The next function will be called when the level changes
  useEffect(() => {
    if (editor) {
      const uri = monaco.Uri.parse(`file:///level${level}`)
      const model = monaco.editor.createModel('', 'lean4', uri)

      editor.setModel(model)
      infoviewApi.serverRestarted(leanClient.initializeResult)
      infoProvider.openPreview(editor, infoviewApi)

      new AbbreviationRewriter(new AbbreviationProvider(), model, editor)

      // setInfoProvider(infoProvider)
      // setInfoviewApi(infoviewApi)

      leanClient.sendRequest("loadLevel", {world: "TestWorld", level}).then((res) => {
        setLevelTitle("Level " + res["index"] + ": " + res["title"])
        setIndex(parseInt(res["index"]))
        setTacticDocs(res["tactics"])
        setLemmaDocs(res["lemmas"])
        setIntroduction(res["introduction"])
        processResponse(res)
      });

      return () => { model.dispose(); }
    }
  }, [editor, level, leanClient])

  function loadLevel(index) {
    setCompleted(false)
    setHistory([])
    setCurLevel(index)
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
        <Button disabled={index <= 1} onClick={() => { loadLevel(index - 1) }} sx={{ ml: 3, mt: 2, mb: 2 }} disableFocusRipple>Previous Level</Button>
        <Button disabled={index >= nbLevels} onClick={() => { loadLevel(index + 1) }} sx={{ ml: 3, mt: 2, mb: 2 }} disableFocusRipple>Next Level</Button>
        <div ref={infoviewRef} className="infoview vscode-light"></div>
        {/* <TacticState goals={leanData.goals} errors={errors} lastTactic={lastTactic} completed={completed} /> */}
      </Grid>
    </Grid>
  )
}

export default Level
