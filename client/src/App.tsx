import * as React from 'react';
import { useState, useEffect } from 'react';
import { MathJaxContext } from "better-react-mathjax";
import * as rpc from 'vscode-ws-jsonrpc';

import '@fontsource/roboto/300.css';
import '@fontsource/roboto/400.css';
import '@fontsource/roboto/500.css';
import '@fontsource/roboto/700.css';

import { AppBar, CssBaseline, Toolbar, Typography } from '@mui/material';

import Welcome from './components/Welcome';
import Level from './components/Level';
import GoodBye from './components/GoodBye';
import useWebSocket from 'react-use-websocket';

function App() {
  const [title, setTitle] = useState("")
  const [conclusion, setConclusion] = useState("")
  const [levelTitle, setLevelTitle] = useState("")
  const [nbLevels, setNbLevels] = useState(0)
  const [curLevel, setCurLevel] = useState(0)
  const [finished, setFinished] = useState(false)
  const [rpcConnection, setRpcConnection] = useState<null|rpc.MessageConnection>(null)

  const socketUrl = ((window.location.protocol === "https:") ? "wss://" : "ws://") + window.location.host + '/websocket/'

  useWebSocket(socketUrl, {
    onOpen: function (ev) {
      const logger = new rpc.ConsoleLogger();
      const socket = rpc.toSocket(ev.target as WebSocket);
      let rpcConnection = rpc.createWebSocketConnection(socket, logger)
      setRpcConnection(rpcConnection);
      rpcConnection.listen();
    }
  })

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
    mainComponent = <Level rpcConnection={rpcConnection} nbLevels={nbLevels} level={curLevel} setCurLevel={setCurLevel} setLevelTitle={setLevelTitle} setFinished={setFinished}/>
  } else {
    mainComponent = <Welcome rpcConnection={rpcConnection} setNbLevels={setNbLevels} setTitle={setTitle} startGame={startGame} setConclusion={setConclusion}/>
  }

  return (
    <div className="App">
    <MathJaxContext config={mathJaxConfig}>
      <CssBaseline />
      <AppBar position="sticky" sx={{ zIndex: (theme) => theme.zIndex.drawer + 1 }}>
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
