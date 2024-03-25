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
import i18n from './i18n';

export const GameIdContext = React.createContext<string>(undefined);

function App() {

  const params = useParams()
  const gameId = "g/" + params.owner + "/" + params.repo

  const {mobile, layout, isSavePreferences, language, setLayout, setIsSavePreferences, setLanguage} = UsePreferences()

  React.useEffect(() => {
    i18n.changeLanguage(language)
  }, [language])

  return (
    <div className="app">
      <GameIdContext.Provider value={gameId}>
          <PreferencesContext.Provider value={{mobile, layout, isSavePreferences, language, setLayout, setIsSavePreferences, setLanguage}}>
            <React.Suspense>
              <Outlet />
            </React.Suspense>
          </PreferencesContext.Provider>
      </GameIdContext.Provider>
    </div>
  )
}

export default App
