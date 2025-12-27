import * as React from 'react';
import { Outlet, useParams } from "react-router-dom";

import '@fontsource/roboto/300.css';
import '@fontsource/roboto/400.css';
import '@fontsource/roboto/500.css';
import '@fontsource/roboto/700.css';

import './css/reset.css';
import './css/app.css';
import { HistoryContext, PreferencesContext, WorldLevelIdContext} from './components/infoview/context';
import { NO_HISTORY_INDEX } from './components/infoview/typewriter';
import UsePreferences from "./state/hooks/use_preferences"
import i18n from './i18n';
import { Popup } from './components/popup/popup';

export const GameIdContext = React.createContext<string>(undefined);

function App() {

  const params = useParams()
  const gameId = "g/" + params.owner + "/" + params.repo
  const levelId = parseInt(params.levelId)
  const worldId = params.worldId

  const {mobile, layout, isSavePreferences, language, isSuggestionsMobileMode, setLayout, setIsSavePreferences, setLanguage, setIsSuggestionsMobileMode} = UsePreferences()

  // Typewriter history state (persists across game levels)
  const [history, setHistory] = React.useState<string[]>([])

  React.useEffect(() => {
    i18n.changeLanguage(language)
  }, [language])

  return (
    <div className="app">
      <GameIdContext.Provider value={gameId}>
          <WorldLevelIdContext.Provider value={{worldId, levelId}}>
          <PreferencesContext.Provider value={{mobile, layout, isSavePreferences, language, isSuggestionsMobileMode, setLayout, setIsSavePreferences, setLanguage, setIsSuggestionsMobileMode}}>
            <HistoryContext.Provider value={{history, setHistory}}>
              <React.Suspense>
                <Outlet />
              </React.Suspense>
              <Popup />
            </HistoryContext.Provider>
          </PreferencesContext.Provider>
          </WorldLevelIdContext.Provider>
      </GameIdContext.Provider>
    </div>
  )
}

export default App
