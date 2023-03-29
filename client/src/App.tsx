import * as React from 'react';
import { useState, useEffect } from 'react';
import { Outlet, useParams } from "react-router-dom";

import '@fontsource/roboto/300.css';
import '@fontsource/roboto/400.css';
import '@fontsource/roboto/500.css';
import '@fontsource/roboto/700.css';

import './reset.css';
import './app.css';

export const GameIdContext = React.createContext<string>(undefined);

function App() {
  const params = useParams();
  return (
    <div className="app">
      <GameIdContext.Provider value={params.gameId}>
        <Outlet />
      </GameIdContext.Provider>
    </div>
  )
}

export default App
