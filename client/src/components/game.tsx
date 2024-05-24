import * as React from 'react'
import { useEffect, useRef } from 'react'
import Split from 'react-split'
import { Box, CircularProgress } from '@mui/material'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faArrowRight } from '@fortawesome/free-solid-svg-icons'

import { GameIdContext } from '../app'
import { useAppDispatch, useAppSelector } from '../hooks'
import { changedOpenedIntro, selectOpenedIntro } from '../state/progress'
import { useGetGameInfoQuery, useLoadInventoryOverviewQuery, useLoadLevelQuery } from '../state/api'
import { Button } from './button'
import { PageContext, PreferencesContext } from './infoview/context'
import { InventoryPanel } from './inventory'
import { ErasePopup } from './popup/erase'
import { InfoPopup } from './popup/info'
import { PrivacyPolicyPopup } from './popup/privacy'
import { UploadPopup } from './popup/upload'
import { PreferencesPopup} from "./popup/preferences"
import { WorldTreePanel } from './world_tree'

import '../css/game.css'
import '../css/welcome.css'
import '../css/level.css'
import { Hint } from './hints'
import i18next from 'i18next'
import { useTranslation } from 'react-i18next'
import { LoadingIcon } from './utils'
import { ChatPanel } from './chat'
import { DualEditor } from './infoview/main'
import { Level } from './level'

/** main page of the game showing among others the tree of worlds/levels */
function Game() {

  const codeviewRef = useRef<HTMLDivElement>(null)

  const { gameId, worldId, levelId } = React.useContext(GameIdContext)

  // Load the namespace of the game
  i18next.loadNamespaces(gameId)

  const {mobile} = React.useContext(PreferencesContext)
  const {isSavePreferences, language, setIsSavePreferences, setLanguage} = React.useContext(PreferencesContext)

  const gameInfo = useGetGameInfoQuery({game: gameId})
  const inventory = useLoadInventoryOverviewQuery({game: gameId})

  const levelInfo = useLoadLevelQuery({game: gameId, world: worldId, level: levelId})


  const {page, setPage} = React.useContext(PageContext)

  // TODO: recover `openedIntro` functionality

  // const [pageNumber, setPageNumber] = React.useState(openedIntro ? 1 : 0)

  // pop-ups
  const [eraseMenu, setEraseMenu] = React.useState(false)
  const [impressum, setImpressum] = React.useState(false)
  const [privacy, setPrivacy] = React.useState(false)
  const [info, setInfo] = React.useState(false)
  const [rulesHelp, setRulesHelp] = React.useState(false)
  const [uploadMenu, setUploadMenu] = React.useState(false)
  const [preferencesPopup, setPreferencesPopup] = React.useState(false)

  // set the window title
  useEffect(() => {
    if (gameInfo.data?.title) {
      window.document.title = gameInfo.data.title
    }
  }, [gameInfo.data?.title])

  return mobile ?
    <div className="app-content mobile">
      {<>
        <ChatPanel visible={worldId ? (levelId == 0 && page == 1) :(page == 0)} />
        { worldId ?
          <Level visible={levelId > 0 && page == 1} /> :
          <WorldTreePanel visible={page == 1} />
        }
        <InventoryPanel visible={page == 2} />
      </>
      }
    </div>
  :
    <Split className="app-content" minSize={0} snapOffset={200}  sizes={[25, 50, 25]}>
      <ChatPanel />
      <div>
        {/* Note: apparently without this `div` the split panel bugs out. */}
        {worldId ? <Level /> : <WorldTreePanel /> }
      </div>
      <InventoryPanel />
    </Split>

}

export default Game
function useLevelEditor(codeviewRef: React.MutableRefObject<HTMLDivElement>, initialCode: any, initialSelections: any, onDidChangeContent: any, onDidChangeSelection: any): { editor: any; infoProvider: any; editorConnection: any } {
  throw new Error('Function not implemented.')
}
