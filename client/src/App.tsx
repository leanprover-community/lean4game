import * as React from 'react';
import { useState, useEffect } from 'react';
import { Outlet } from "react-router-dom";

import '@fontsource/roboto/300.css';
import '@fontsource/roboto/400.css';
import '@fontsource/roboto/500.css';
import '@fontsource/roboto/700.css';

import { AppBar, CssBaseline, Toolbar, Typography } from '@mui/material';

import { useAppSelector } from './hooks';

type SetTitleType = {setTitle: (string) => void, setSubtitle: (string) => void}
export const SetTitleContext = React.createContext<SetTitleType>({setTitle: () => {}, setSubtitle: () => {}})

function App() {
  const [title, setTitle] = useState("")
  const [subtitle, setSubtitle] = useState("")

  return (
    <div className="App">
      <CssBaseline />
      <AppBar className="AppBar" position="sticky" sx={{ zIndex: (theme) => theme.zIndex.drawer + 1 }}>
        <Toolbar sx={{ justifyContent: "space-between" }}>
        <Typography variant="h6" noWrap component="div">
          {title}
        </Typography>
        <Typography variant="h6" noWrap component="div">
          {subtitle}
        </Typography>
        </Toolbar>
      </AppBar>
      <SetTitleContext.Provider value={{setTitle, setSubtitle}}>
        <Outlet />
      </SetTitleContext.Provider>
    </div>
  )
}

export default App
