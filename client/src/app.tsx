import * as React from 'react';
import { Outlet, useParams } from "react-router-dom";

import '@fontsource/roboto/300.css';
import '@fontsource/roboto/400.css';
import '@fontsource/roboto/500.css';
import '@fontsource/roboto/700.css';

import './css/reset.css';
import './css/app.css';
import { MobileContext, PreferencesContext} from './components/infoview/context';
import { AUTO_SWITCH_THRESHOLD, getWindowDimensions, setLayout, setisSavePreferences, PreferencesState} from './state/preferences';
import { useAppDispatch, useAppSelector } from './hooks';

export const GameIdContext = React.createContext<string>(undefined);

function App() {
  const dispatch = useAppDispatch()

  const params = useParams()
  const gameId = "g/" + params.owner + "/" + params.repo

  // TODO: 
  const [mobile, setMobile] = React.useState<boolean>()
  const layout = useAppSelector((state) => state.preferences.layout);
  const changeLayout = (layout: PreferencesState["layout"]) => dispatch(setLayout(layout))
  const isSavePreferences = useAppSelector((state) => state.preferences.isSavePreferences);
  const changeIsSavePreferences = (isSave: boolean) => dispatch(setisSavePreferences(isSave))

  const automaticallyAdjustLayout = () => {
    const {width} = getWindowDimensions()
    setMobile(width < AUTO_SWITCH_THRESHOLD)
  }

  React.useEffect(()=>{
    if (layout === "auto"){
      void automaticallyAdjustLayout()
      window.addEventListener('resize', automaticallyAdjustLayout)

      return () => window.removeEventListener('resize', automaticallyAdjustLayout)
    } else {
      setMobile(layout === "mobile")
    }
  }, [layout])

  return (
    <div className="app">
      <GameIdContext.Provider value={gameId}>
        <MobileContext.Provider value={{mobile, setMobile}}>
          <PreferencesContext.Provider value={{layout, isSavePreferences, setLayout: changeLayout, setIsSavePreferences: changeIsSavePreferences}}>
            <Outlet />
          </PreferencesContext.Provider>
        </MobileContext.Provider>
      </GameIdContext.Provider>
    </div>
  )
}

export default App
