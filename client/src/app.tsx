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
import { selectOpenedIntro } from './state/progress';
import { useSelector } from 'react-redux';

export const GameIdContext = React.createContext<string>(undefined);

function App() {
  const params = useParams()
  const gameId = "g/" + params.owner + "/" + params.repo
  const {width, height} = useWindowDimensions()
  const [mobile, setMobile] = React.useState(width < 800)

  // For mobile only
  const openedIntro = useSelector(selectOpenedIntro(gameId))
  const [pageNumber, setPageNumber] = React.useState(openedIntro ? 1 : 0)

  return (
    <div className="app">
      <GameIdContext.Provider value={gameId}>
        <MobileContext.Provider value={{mobile, setMobile, pageNumber, setPageNumber}}>
          <Outlet />
        </MobileContext.Provider>
      </GameIdContext.Provider>
    </div>
  )
}

export default App
