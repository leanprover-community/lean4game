import * as React from 'react';
import { useEffect, useState, useRef } from 'react';
import '@fontsource/roboto/300.css';
import '@fontsource/roboto/400.css';
import '@fontsource/roboto/500.css';
import '@fontsource/roboto/700.css';

import Grid from '@mui/material/Unstable_Grid2';

import LeftPanel from './LeftPanel';
import InputZone from './InputZone';
import Message from './Message';
import TacticState from './TacticState';
import { LeanClient } from 'lean4web/client/src/editor/leanclient';
import * as monaco from 'monaco-editor/esm/vs/editor/editor.api.js'

interface LevelProps {
  leanClient: null|LeanClient;
  nbLevels: any;
  level: any;
  setCurLevel: any;
  setLevelTitle: any;
  setFinished: any
}

function Level({ leanClient, nbLevels, level, setCurLevel, setLevelTitle, setFinished }: LevelProps) {
  const [index, setIndex] = useState(level) // Level number
  const [tacticDocs, setTacticDocs] = useState([])
  const [lemmaDocs, setLemmaDocs] = useState([])

  const [leanData, setLeanData] = useState({goals: []})
  const [history, setHistory] = useState([])
  const [lastTactic, setLastTactic] = useState("")
  const [errors, setErrors] = useState([])
  const codeviewRef = useRef<HTMLDivElement>(null)

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

  // The next function will be called when the level changes
  useEffect(() => {
    const uri = monaco.Uri.parse('file:///LeanProject/Level1.lean')
    const model = monaco.editor.createModel('', 'lean4', uri)
    const editor = monaco.editor.create(codeviewRef.current!, {
      model,
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
    // setEditor(editor)
    // new AbbreviationRewriter(new AbbreviationProvider(), model, editor)


    // const infoProvider = new InfoProvider(leanClient)
    // const div: HTMLElement = infoviewRef.current!
    // const infoviewApi = renderInfoview(infoProvider.getApi(), div)
    // setInfoProvider(infoProvider)
    // setInfoviewApi(infoviewApi)

    leanClient.sendRequest("loadLevel", {number: level}).then((res) => {
      setLevelTitle("Level " + res["index"] + ": " + res["title"])
      setIndex(parseInt(res["index"]))
      setTacticDocs(res["tactics"])
      setLemmaDocs(res["lemmas"])
      processResponse(res)
    });
  }, [level, leanClient])

  function sendTactic(input) {
    leanClient.sendRequest("runTactic", {tactic: input}).then(processResponse);
    setLastTactic(input);
    setHistory(history.concat([input]));
  }

  function undo() {
    if (errors.length === 0) {
      leanClient.sendRequest('undo', {}).then(processResponse);
    }
    if (history.length > 1) {
      setLastTactic(history[history.length - 1]);
    } else {
      setLastTactic("");
    };
    setErrors([]);
    setHistory(history.slice(0, -1));
  }

  function loadNextLevel() {
    setCompleted(false)
    setHistory([])
    setCurLevel(index + 1)
  }

  function closeMessage() {
    setMessageOpen(false)
  }

  function finishGame() {
    setLevelTitle("")
    setFinished(true)
  }

  return (
    <Grid container sx={{ mt: 3, ml: 1, mr: 1 }} columnSpacing={{ xs: 1, sm: 2, md: 3 }}>
      <Grid xs={4}>
        <LeftPanel spells={tacticDocs} inventory={lemmaDocs} />
      </Grid>
      <Grid xs={4}>
        <div ref={codeviewRef} className="codeview" style={{height: "20em"}}></div>
        {/* <InputZone index={index} history={history} messageOpen={messageOpen} setMessageOpen={setMessageOpen} completed={completed} sendTactic={sendTactic} nbLevels={nbLevels} loadNextLevel={loadNextLevel}
          errors={errors} lastTactic={lastTactic} undo={undo} finishGame={finishGame} /> */}
        <Message isOpen={messageOpen} content={message} close={closeMessage} />
      </Grid>
      <Grid xs={4}>
        <TacticState goals={leanData.goals} errors={errors} lastTactic={lastTactic} completed={completed} />
      </Grid>
    </Grid>
  )
}

export default Level
