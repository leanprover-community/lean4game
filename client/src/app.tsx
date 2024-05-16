import * as React from 'react';
import { Outlet, useParams } from "react-router-dom";
import { useEffect, useState } from 'react';

import '@fontsource/roboto/300.css';
import '@fontsource/roboto/400.css';
import '@fontsource/roboto/500.css';
import '@fontsource/roboto/700.css';

import './css/reset.css';
import './css/app.css';
import { PageContext, PreferencesContext} from './components/infoview/context';
import UsePreferences from "./state/hooks/use_preferences"
import i18n from './i18n';
import { Navigation } from './components/navigation';
import { useSelector } from 'react-redux';
import { changeTypewriterMode, selectOpenedIntro, selectTypewriterMode } from './state/progress';
import { useAppDispatch } from './hooks';
import { Popup, PopupContext } from './components/popup/popup';
import { useGetGameInfoQuery } from './state/api';

export const GameIdContext = React.createContext<{
  gameId: string,
  worldId: string|null,
  levelId: number|null}>({gameId: null, worldId: null, levelId: null});

function App() {

  const params = useParams()
  const gameId = (params.owner && params.repo) ? "g/" + params.owner + "/" + params.repo : null
  const worldId = params.worldId
  const levelId = parseInt(params.levelId)

  const {mobile, layout, isSavePreferences, language, setLayout, setIsSavePreferences, setLanguage} = UsePreferences()

  const dispatch = useAppDispatch()
  const typewriterMode = useSelector(selectTypewriterMode(gameId))
  const setTypewriterMode = (newTypewriterMode: boolean) => dispatch(changeTypewriterMode({game: gameId, typewriterMode: newTypewriterMode}))
  const [lockEditorMode, setLockEditorMode] = useState(false)
  const [typewriterInput, setTypewriterInput] = useState("")
  const [page, setPage] = useState(0)
  const [popupContent, setPopupContent] = useState(null)
  const gameInfo = useGetGameInfoQuery({game: gameId})


  const openedIntro = useSelector(selectOpenedIntro(gameId))

  useEffect(() => {
    if (openedIntro && !worldId && page == 0) {
      setPage(1)
    }
  }, [openedIntro])

  useEffect(() => {
    let availableLangs = gameInfo.data?.tile?.languages
    if (gameId && availableLangs?.length > 0 && !(availableLangs.includes(language))) {
      // if the game is not available in the preferred language, display it in the original
      // language
      console.debug(`using default language: ${availableLangs[0]}`)
      i18n.changeLanguage(availableLangs[0])
    } else {
      console.debug(`using language: ${language}`)
      i18n.changeLanguage(language)
    }
  }, [gameId, gameInfo.data?.tile?.languages, language])

  return (
    <div className="app">
      <GameIdContext.Provider value={{gameId, worldId, levelId}}>
        <PreferencesContext.Provider value={{mobile, layout, isSavePreferences, language, setLayout, setIsSavePreferences, setLanguage}}>
          <PopupContext.Provider value={{popupContent, setPopupContent}}>
            <PageContext.Provider value={{typewriterMode, setTypewriterMode, typewriterInput, setTypewriterInput, lockEditorMode, setLockEditorMode, page, setPage}}>
              <Navigation />
              <React.Suspense>
                <Outlet />
              </React.Suspense>
            </PageContext.Provider>
            { popupContent && <Popup /> }
          </PopupContext.Provider>
        </PreferencesContext.Provider>
      </GameIdContext.Provider>
    </div>
  )
}

export default App
