import * as React from 'react';
import { Outlet, useParams } from "react-router-dom";

import '@fontsource/roboto/300.css';
import '@fontsource/roboto/400.css';
import '@fontsource/roboto/500.css';
import '@fontsource/roboto/700.css';

import './css/reset.css';
import './css/app.css';
import { MobileContext } from './components/infoview/context';
import { useMobile } from './hooks';
import { AUTO_SWITCH_THRESHOLD, getWindowDimensions} from './state/preferences';
import { connection } from './connection';

export const GameIdContext = React.createContext<string>(undefined);

function App() {
  const { mobile, setMobile, lockMobile, setLockMobile } = useMobile();

  const params = useParams()
  const gameId = "g/" + params.owner + "/" + params.repo

  const automaticallyAdjustLayout = () => {
    const {width} = getWindowDimensions()
    setMobile(width < AUTO_SWITCH_THRESHOLD)
  }

  React.useEffect(()=>{
    if (!lockMobile){
      void automaticallyAdjustLayout()
      window.addEventListener('resize', automaticallyAdjustLayout)

      return () => {
        window.removeEventListener('resize', automaticallyAdjustLayout)
      }
    }
  }, [lockMobile])

  React.useEffect(() => {
    connection.startLeanClient(gameId);
  }, [gameId])

  return (
    <div className="app">
      <GameIdContext.Provider value={gameId}>
        <MobileContext.Provider value={{mobile, setMobile, lockMobile, setLockMobile}}>
          <Outlet />
        </MobileContext.Provider>
      </GameIdContext.Provider>
    </div>
  )
}

export default App
