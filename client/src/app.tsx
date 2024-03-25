import * as React from 'react';
import { Outlet, useParams } from "react-router-dom";

import '@fontsource/roboto/300.css';
import '@fontsource/roboto/400.css';
import '@fontsource/roboto/500.css';
import '@fontsource/roboto/700.css';

import './css/reset.css';
import './css/app.css';
import { PreferencesContext} from './components/infoview/context';
import UsePreferences from "./state/hooks/use_preferences"

export const GameIdContext = React.createContext<string>(undefined);

function App() {

  const params = useParams()
  const gameId = "g/" + params.owner + "/" + params.repo

  const {mobile, layout, isSavePreferences, setLayout, setIsSavePreferences} = UsePreferences()

  return (
    <div className="app">
      <GameIdContext.Provider value={gameId}>
          <PreferencesContext.Provider value={{mobile, layout, isSavePreferences, setLayout, setIsSavePreferences}}>
            <React.Suspense>
              <Outlet />
            </React.Suspense>
          </PreferencesContext.Provider>
      </GameIdContext.Provider>
    </div>
  )
}

export default App
