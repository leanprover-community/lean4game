import * as React from 'react'
import { useEffect } from 'react'
import Split from 'react-split'
import { Box, CircularProgress } from '@mui/material'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faArrowRight } from '@fortawesome/free-solid-svg-icons'

import { Button } from './button'
import { WorldTreePanel } from './world_tree'

import '../css/welcome.css'
import { WelcomeAppBar } from './app_bar'
import { Hint } from './hints'
import i18next from 'i18next'
import { useGameTranslation } from '../utils/translation'
import { InventoryPanel } from './inventory/inventory_panel'
import { gameIdAtom } from '../store/location-atoms'
import { useAtom } from 'jotai'
import { readGameIntroAtom } from '../store/chat-atoms'
import { gameInfoAtom } from '../store/query-atoms'
import { inventoryOverviewAtom } from '../store/inventory-atoms'
import { mobileAtom } from '../store/preferences-atoms'


/** the panel showing the game's introduction text */
function IntroductionPanel({setPageNumber}: {setPageNumber: (val: number) => void}) {
  const [mobile] = useAtom(mobileAtom)
  const [{ data: gameInfo, isLoading: gameInfoIsLoading }] = useAtom(gameInfoAtom)
  const [, setReadGameIntro] = useAtom(readGameIntroAtom)


  const { t : gT } = useGameTranslation()


  // TODO: I left the setup for splitting up the introduction in place, but if it's not needed
  // then this can be simplified.

  // let text: Array<string> = introduction.split(/\n(\s*\n)+/)
  let text: Array<string> = gameInfo?.introduction ? [gT(gameInfo.introduction)] : []

  return <div className="column chat-panel">
    <div className="chat">
      {text?.map(((t, i) =>
        t.trim() ?
          <Hint key={`intro-p-${i}`}
            hint={{text: t, hidden: false, rawText: t, varNames: []}}
            step={0} selected={undefined} toggleSelection={undefined} />
        : <></>
      ))}
    </div>
    {mobile &&
      <div className="button-row">
        <Button className="btn"
          title="" onClick={() => {
            setPageNumber(1);
            setReadGameIntro(true)
          }}>
          Start&nbsp;<FontAwesomeIcon icon={faArrowRight}/>
        </Button>
      </div>
    }
  </div>
}

/** main page of the game showing among others the tree of worlds/levels */
function Welcome() {
  const [gameId] = useAtom(gameIdAtom)
  const [readGameIntro] = useAtom(readGameIntroAtom)
  const [{ data: gameInfo, isLoading: gameInfoIsLoading }] = useAtom(gameInfoAtom)
  const [{ data: inventory }] = useAtom(inventoryOverviewAtom)

  // Load the namespace of the game
  i18next.loadNamespaces(gameId ?? "")

  const [mobile] = useAtom(mobileAtom)


  // For mobile only
  const [pageNumber, setPageNumber] = React.useState(readGameIntro ? 1 : 0)

  // set the window title
  useEffect(() => {
    if (gameInfo?.title) {
      window.document.title = gameInfo.title
    }
  }, [gameInfo?.title])

  return gameInfoIsLoading ?
    <Box display="flex" alignItems="center" justifyContent="center" sx={{ height: "calc(100vh - 64px)" }}>
      <CircularProgress />
    </Box>
  : <>
    <WelcomeAppBar pageNumber={pageNumber} setPageNumber={setPageNumber} />
    <div className="app-content">
      { mobile ?
          <div className="welcome mobile">
            {(pageNumber == 0 ?
              <IntroductionPanel setPageNumber={setPageNumber} />
            : pageNumber == 1 ?
              <WorldTreePanel />
            :
              <InventoryPanel levelInfo={inventory} />
            )}
          </div>
        :
          <Split className="welcome" minSize={0} snapOffset={200}  sizes={[25, 50, 25]}>
            <IntroductionPanel setPageNumber={setPageNumber} />
            <WorldTreePanel />
            <InventoryPanel levelInfo={inventory} />
          </Split>
      }
    </div>
  </>
}

export default Welcome
