import * as React from 'react';
import { Outlet, useParams } from "react-router-dom";

import '@fontsource/roboto/300.css';
import '@fontsource/roboto/400.css';
import '@fontsource/roboto/500.css';
import '@fontsource/roboto/700.css';

import './css/reset.css';
import './css/app.css';
import { MobileContext } from './components/infoview/context';
import { useWindowDimensions } from './window_width';

export const GameIdContext = React.createContext<string>(undefined);

function App() {
  const params = useParams()
  const gameId = "g/" + params.owner + "/" + params.repo
  const {width, height} = useWindowDimensions()
  const [mobile, setMobile] = React.useState(width < 800)

  return (
    <div className="app">
      <GameIdContext.Provider value={gameId}>
        <MobileContext.Provider value={{mobile, setMobile}}>
          <Outlet />
        </MobileContext.Provider>
      </GameIdContext.Provider>
    </div>
  )
}

export default App
