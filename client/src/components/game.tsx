import * as React from 'react'
import { useContext, useEffect, useRef, useState } from 'react'
import Split from 'react-split'
import { Box, CircularProgress } from '@mui/material'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faArrowRight } from '@fortawesome/free-solid-svg-icons'

import { GameIdContext } from '../app'
import { useAppDispatch, useAppSelector } from '../hooks'
import { changeTypewriterMode, changedReadIntro, changedSelection, codeEdited, selectCode, selectReadIntro, selectSelections, selectTypewriterMode } from '../state/progress'
import { useGetGameInfoQuery, useLoadInventoryOverviewQuery, useLoadLevelQuery } from '../state/api'
import { Button } from './button'
import { ChatContext, PageContext, PreferencesContext, ProofContext } from './infoview/context'
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
import i18next from 'i18next'
import { useTranslation } from 'react-i18next'
import { LoadingIcon } from './utils'
import { ChatPanel } from './chat'
import { DualEditor } from './infoview/main'
import { Level, LevelWrapper } from './level'
import { GameHint, ProofState } from './infoview/rpc_api'
import { useSelector } from 'react-redux'
import { Diagnostic } from 'vscode-languageserver-types'

/** main page of the game showing among others the tree of worlds/levels */
function Game() {

  const { gameId, worldId, levelId } = React.useContext(GameIdContext)

  // Load the namespace of the game
  i18next.loadNamespaces(gameId)

  const {mobile} = useContext(PreferencesContext)
  const {isSavePreferences, language, setIsSavePreferences, setLanguage} = React.useContext(PreferencesContext)

  const gameInfo = useGetGameInfoQuery({game: gameId})
  const inventory = useLoadInventoryOverviewQuery({game: gameId})

  const levelInfo = useLoadLevelQuery({game: gameId, world: worldId, level: levelId})

  const {page, setPage} = useContext(PageContext)

  // TODO: recover `readIntro` functionality

  // const [pageNumber, setPageNumber] = React.useState(readIntro ? 1 : 0)

  const chatRef = useRef<HTMLDivElement>(null)
  // When deleting the proof, we want to keep to old messages around until
  // a new proof has been entered. e.g. to consult messages coming from dead ends
  const [deletedChat, setDeletedChat] = useState<Array<GameHint>>([])
  // A set of row numbers where help is displayed
  const [showHelp, setShowHelp] = useState<Set<number>>(new Set())
  // Select and highlight proof steps and corresponding hints
  // TODO: with the new design, there is no difference between the introduction and
  // a hint at the beginning of the proof...
  const [selectedStep, setSelectedStep] = useState<number>(null)

  // The state variables for the `ProofContext`
  const [proof, setProof] = useState<ProofState>({steps: [], diagnostics: [], completed: false, completedWithWarnings: false})
  const [interimDiags, setInterimDiags] = useState<Array<Diagnostic>>([])
  const [isCrashed, setIsCrashed] = useState<Boolean>(false)


  const dispatch = useAppDispatch()

  const typewriterMode = useSelector(selectTypewriterMode(gameId))
  const setTypewriterMode = (newTypewriterMode: boolean) => dispatch(changeTypewriterMode({game: gameId, typewriterMode: newTypewriterMode}))

  const initialCode = useAppSelector(selectCode(gameId, worldId, levelId))
  const initialSelections = useAppSelector(selectSelections(gameId, worldId, levelId))

  // set the window title
  useEffect(() => {
    if (gameInfo.data?.title) {
      window.document.title = gameInfo.data.title
    }
  }, [gameInfo.data?.title])

  // Delete the current proof on changing level
  useEffect(() => {
    setProof(null)
    setSelectedStep(null)
    setDeletedChat([])
    setShowHelp(new Set())
  }, [gameId, worldId, levelId])

  return <ChatContext.Provider value={{selectedStep, setSelectedStep, deletedChat, setDeletedChat, showHelp, setShowHelp, chatRef}}>
    <ProofContext.Provider value={{proof, setProof, interimDiags, setInterimDiags, crashed: isCrashed, setCrashed: setIsCrashed}}>
    { mobile ?
      <div className="app-content mobile">
        {<>
          <ChatPanel visible={worldId ? (levelId == 0 && page == 1) :(page == 0)} />
          { worldId ?
            <LevelWrapper visible={page == 1} /> :
            <WorldTreePanel visible={page == 1} />
          }
          <InventoryPanel visible={page == 2} />
        </>
        }
      </div>
    :
      <Split className="app-content" minSize={0} snapOffset={200}  sizes={[25, 50, 25]}>
        <ChatPanel />
        <div className="column">
          {/* Note: apparently without this `div` the split panel bugs out. */}
          {worldId ? <LevelWrapper /> : <WorldTreePanel /> }
        </div>
        <InventoryPanel />
        </Split>
    }
    </ProofContext.Provider>
  </ChatContext.Provider>

}

export default Game
function useLevelEditor(codeviewRef: React.MutableRefObject<HTMLDivElement>, initialCode: any, initialSelections: any, onDidChangeContent: any, onDidChangeSelection: any): { editor: any; infoProvider: any; editorConnection: any } {
  throw new Error('Function not implemented.')
}
