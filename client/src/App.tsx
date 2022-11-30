import * as React from 'react';
import { useState, useEffect } from 'react';
import { MathJaxContext } from "better-react-mathjax";
import * as rpc from 'vscode-ws-jsonrpc';
import * as monaco from 'monaco-editor/esm/vs/editor/editor.api.js'

import '@fontsource/roboto/300.css';
import '@fontsource/roboto/400.css';
import '@fontsource/roboto/500.css';
import '@fontsource/roboto/700.css';

import { AppBar, CssBaseline, Toolbar, Typography } from '@mui/material';

import Welcome from './components/Welcome';
import Level from './components/Level';
import GoodBye from './components/GoodBye';
import { monacoSetup } from 'lean4web/client/src/monacoSetup'
import { useAppSelector } from './hooks';

function App() {
  const [conclusion, setConclusion] = useState("")
  const [levelTitle, setLevelTitle] = useState("")
  const [nbLevels, setNbLevels] = useState(0)
  const [curLevel, setCurLevel] = useState(0)
  const [finished, setFinished] = useState(false)

  const mathJaxConfig = {
    loader: {
      load: ['input/tex-base', 'output/svg']
      },
        tex: {
      inlineMath: [['$', '$'], ['\\(', '\\)']]
      },
    svg: {
      fontCache: 'global'
    }
    }

  function startGame() {
    setCurLevel(1)
  }

  let mainComponent;
  if (finished) {
    mainComponent = <GoodBye message={conclusion} />
  } else if (curLevel > 0) {
    mainComponent = <Level nbLevels={5} level={curLevel} setCurLevel={setCurLevel} setLevelTitle={setLevelTitle} setFinished={setFinished}/>
  } else {
    mainComponent = <Welcome setNbLevels={setNbLevels} startGame={startGame} setConclusion={setConclusion}/>
  }

  const title = useAppSelector(state => state.game.title)

  return (
    <div className="App">
    <MathJaxContext config={mathJaxConfig}>
      <CssBaseline />
      <AppBar className="AppBar" position="sticky" sx={{ zIndex: (theme) => theme.zIndex.drawer + 1 }}>
        <Toolbar sx={{ justifyContent: "space-between" }}>
        <Typography variant="h6" noWrap component="div">
          {title}
        </Typography>
        <Typography variant="h6" noWrap component="div">
          {levelTitle}
        </Typography>
        </Toolbar>
      </AppBar>
      {mainComponent}
    </MathJaxContext>
    </div>
  )
}

export default App
