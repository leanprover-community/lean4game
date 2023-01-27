import * as React from 'react';
import { useState, useEffect } from 'react';
import { Outlet } from "react-router-dom";

import '@fontsource/roboto/300.css';
import '@fontsource/roboto/400.css';
import '@fontsource/roboto/500.css';
import '@fontsource/roboto/700.css';

import './reset.css';
import './app.css';

type SetTitleType = {setTitle: (string) => void, setSubtitle: (string) => void}
export const SetTitleContext = React.createContext<SetTitleType>({setTitle: () => {}, setSubtitle: () => {}})

function App() {
  const [title, setTitle] = useState("")
  const [subtitle, setSubtitle] = useState("")

  return (
    <div className="app">
      <SetTitleContext.Provider value={{setTitle, setSubtitle}}>
        <Outlet />
      </SetTitleContext.Provider>
    </div>
  )
}

export default App
