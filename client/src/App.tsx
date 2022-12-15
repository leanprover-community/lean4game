import * as React from 'react';
import { useState, useEffect } from 'react';
import { Outlet } from "react-router-dom";

import '@fontsource/roboto/300.css';
import '@fontsource/roboto/400.css';
import '@fontsource/roboto/500.css';
import '@fontsource/roboto/700.css';

import { AppBar, CssBaseline, Toolbar, Typography } from '@mui/material';

import { useAppSelector } from './hooks';

function App() {
  const [conclusion, setConclusion] = useState("")
  const [levelTitle, setLevelTitle] = useState("")
  const [nbLevels, setNbLevels] = useState(0)
  const [curLevel, setCurLevel] = useState(0)
  const [finished, setFinished] = useState(false)

  function startGame() {
    setCurLevel(1)
  }

  const title = ""//useAppSelector(state => state.gameApi.data.title)

  return (
    <div className="App">
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
      <Outlet />
    </div>
  )
}

export default App
