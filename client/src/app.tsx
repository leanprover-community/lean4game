import * as React from 'react';
import { Outlet, useParams } from "react-router-dom";

import '@fontsource/roboto/300.css';
import '@fontsource/roboto/400.css';
import '@fontsource/roboto/500.css';
import '@fontsource/roboto/700.css';

import './reset.css';
import './app.css';
import { MobileContext } from './components/infoview/context';
import { useWindowDimensions } from './window_width';
import { selectOpenedIntro } from './state/progress';
import { useSelector } from 'react-redux';

export const GameIdContext = React.createContext<string>(undefined);

function App() {
  const params = useParams()
  const gameId = "g/" + params.owner + "/" + params.repo

  // TODO: Make mobileLayout be changeable in settings
  // TODO: Handle resize Events
  const {width, height} = useWindowDimensions()
  const [mobile, setMobile] = React.useState(width < 800)

  // On mobile, there are multiple pages on the welcome page to switch between
  const openedIntro = useSelector(selectOpenedIntro(gameId))
  // On mobile, there are multiple pages to switch between
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
