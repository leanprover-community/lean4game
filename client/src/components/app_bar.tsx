/**
 *  @file contains the navigation bars of the app.
 */
import * as React from 'react'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faDownload, faUpload, faEraser, faBook, faBookOpen, faGlobe, faHome,
  faArrowRight, faArrowLeft, faXmark, faBars, faCode,
  faCircleInfo, faTerminal, faMobileScreenButton, faDesktop, faGear } from '@fortawesome/free-solid-svg-icons'
import { GameIdContext } from "../app"
import { InputModeContext, PreferencesContext, WorldLevelIdContext } from "./infoview/context"
import { GameInfo, useGetGameInfoQuery } from '../state/api'
import { changedOpenedIntro, selectCompleted, selectDifficulty, selectProgress } from '../state/progress'
import { useAppDispatch, useAppSelector } from '../hooks'
import { Button } from './button'
import { downloadProgress } from './popup/erase'
import ReactCountryFlag from "react-country-flag"

/** navigation buttons for mobile welcome page to switch between intro/tree/inventory. */
function MobileNavButtons({pageNumber, setPageNumber}:
  { pageNumber: number,
    setPageNumber: any}) {
  const gameId = React.useContext(GameIdContext)
  const dispatch = useAppDispatch()

  // if `prevText` or `prevIcon` is set, show a button to go back
  let prevText  = {0: null, 1: "Intro", 2: null}[pageNumber]
  let prevIcon  = {0: null, 1: null, 2: faBookOpen}[pageNumber]
  let prevTitle = {0: null, 1: "Game Introduction", 2: "World selection"}[pageNumber]
  // if `nextText` or `nextIcon` is set, show a button to go forward
  let nextText  = {0: "Start", 1: null, 2: null}[pageNumber]
  let nextIcon  = {0: null, 1: faBook, 2: null}[pageNumber]
  let nextTitle = {0: "World selection", 1: "Inventory", 2: null}[pageNumber]

  return <>
    {(prevText || prevIcon) &&
      <Button className="btn btn-inverted toggle-width" to={pageNumber == 0 ? "/" : ""}
          inverted="true" title={prevTitle}
          onClick={() => {pageNumber == 0 ? null : setPageNumber(pageNumber - 1)}}>
        {prevIcon && <FontAwesomeIcon icon={prevIcon} />}
        {prevText && `${prevText}`}
      </Button>
    }
    {(nextText || nextIcon) &&
      <Button className="btn btn-inverted toggle-width" to="" inverted="true"
          title={nextTitle} onClick={() => {
            console.log(`page number: ${pageNumber}`)
            setPageNumber(pageNumber+1);
            dispatch(changedOpenedIntro({game: gameId, openedIntro: true}))}}>
        {nextText && `${nextText}`}
        {nextIcon && <FontAwesomeIcon icon={nextIcon} />}
      </Button>
    }
  </>
}

/** button to toggle dropdown menu. */
function MenuButton({navOpen, setNavOpen}) {
  return <Button to="" className="btn toggle-width" id="menu-btn" onClick={(ev) => {setNavOpen(!navOpen)}}>
    {navOpen ? <FontAwesomeIcon icon={faXmark} /> : <FontAwesomeIcon icon={faBars} />}
  </Button>
}

/** button to go one level futher.
 * for the last level, this button turns into a button going back to the welcome page.
 */
function NextButton({worldSize, difficulty, completed, setNavOpen}) {
  const gameId = React.useContext(GameIdContext)
  const {worldId, levelId} = React.useContext(WorldLevelIdContext)
  return (levelId < worldSize ?
    <Button inverted="true"
        to={`/${gameId}/world/${worldId}/level/${levelId + 1}`} title="next level"
        disabled={difficulty >= 2 && !(completed || levelId == 0)}
        onClick={() => setNavOpen(false)}>
      <FontAwesomeIcon icon={faArrowRight} />&nbsp;{levelId ? "Next" : "Start"}
    </Button>
    :
    <Button to={`/${gameId}`} inverted="true" title="back to world selection" id="home-btn">
      <FontAwesomeIcon icon={faHome} />&nbsp;Leave World
    </Button>
  )
}

/** button to go one level back.
 * only renders if the current level id is > 0.
 */
function PreviousButton({setNavOpen}) {
  const gameId = React.useContext(GameIdContext)
  const {worldId, levelId} = React.useContext(WorldLevelIdContext)
  return (levelId > 0 && <>
    <Button disabled={levelId <= 0} inverted="true"
        to={`/${gameId}/world/${worldId}/level/${levelId - 1}`}
        title="previous level"
        onClick={() => setNavOpen(false)}>
      <FontAwesomeIcon icon={faArrowLeft} />&nbsp;Previous
    </Button>
  </>)
}

/** button to toggle between editor and typewriter */
function InputModeButton({setNavOpen, isDropdown}) {
  const {levelId} = React.useContext(WorldLevelIdContext)
  const {typewriterMode, setTypewriterMode, lockEditorMode} = React.useContext(InputModeContext)

  /** toggle input mode if allowed */
  function toggleInputMode(ev: React.MouseEvent) {
    if (!lockEditorMode){
      setTypewriterMode(!typewriterMode)
      setNavOpen(false)
    }
  }

  return <Button
      className={`btn btn-inverted ${isDropdown? '' : 'toggle-width'}`} disabled={levelId <= 0 || lockEditorMode}
      inverted="true" to=""
      onClick={(ev) => toggleInputMode(ev)}
      title={lockEditorMode ? "Editor mode is enforced!" : typewriterMode ? "Editor mode" : "Typewriter mode"}>
    <FontAwesomeIcon icon={(typewriterMode && !lockEditorMode) ? faCode : faTerminal} />
    {isDropdown && ((typewriterMode && !lockEditorMode) ? <>&nbsp;Editor mode</> : <>&nbsp;Typewriter mode</>)}
  </Button>
}

/** button to toggle iimpressum popup */
function ImpressumButton({setNavOpen, toggleImpressum, isDropdown}) {
  return <Button className="btn btn-inverted toggle-width"
    title="information, Impressum, privacy policy" inverted="true" to="" onClick={(ev) => {toggleImpressum(ev); setNavOpen(false)}}>
    <FontAwesomeIcon icon={faCircleInfo} />
    {isDropdown && <>&nbsp;Info &amp; Impressum</>}
  </Button>
}

/** button to toggle iimpressum popup */
function LanguageButton({setNavOpen, toggleLangNav, isDropdown}) {
  return <Button className="btn btn-inverted language-btn"
    title="language" inverted="true" to="" onClick={(ev) => {toggleLangNav(ev); setNavOpen(false)}}>
    <ReactCountryFlag countryCode="GB"
      className="emojiFlag"
      style={{
          height: '1.3em',
          width: '1.6em',
      }}
      title="English"
    />
    {isDropdown && <>&nbsp;Language</>}
  </Button>
}

/**  button to go back to welcome page */
function HomeButton({isDropdown}) {
  const gameId = React.useContext(GameIdContext)
  return <Button to={`/${gameId}`} inverted="true" title="back to world selection" id="home-btn">
    <FontAwesomeIcon icon={faHome} />
    {isDropdown && <>&nbsp;Home</>}
  </Button>
}

/** button in mobile level to toggle inventory.
 * only displays a button if `setPageNumber` is set.
 */
function InventoryButton({pageNumber, setPageNumber}) {
  return (setPageNumber &&
    <Button to="" className="btn btn-inverted toggle-width"
      title={pageNumber ? "close inventory" : "show inventory"}
      inverted="true" onClick={() => {setPageNumber(pageNumber ? 0 : 1)}}>
      <FontAwesomeIcon icon={pageNumber ? faBookOpen : faBook} />
    </Button>
  )
}

/** the navigation bar on the welcome page */
export function WelcomeAppBar({pageNumber, setPageNumber, gameInfo, toggleImpressum, toggleEraseMenu, toggleUploadMenu, toggleInfo, togglePreferencesPopup} : {
  pageNumber: number,
  setPageNumber: any,
  gameInfo: GameInfo,
  toggleImpressum: any,
  toggleEraseMenu: any,
  toggleUploadMenu: any,
  toggleInfo: any,
  togglePreferencesPopup: () => void;
}) {
  const gameId = React.useContext(GameIdContext)
  const gameProgress = useAppSelector(selectProgress(gameId))
  const {mobile} = React.useContext(PreferencesContext)
  const [navOpen, setNavOpen] = React.useState(false)

  return <div className="app-bar">
    <div className='app-bar-left'>
      <Button inverted="false" title="back to games selection" to="/">
        <FontAwesomeIcon icon={faArrowLeft} />&nbsp;<FontAwesomeIcon icon={faGlobe} />
      </Button>
      <span className="app-bar-title"></span>
    </div>
    <div>
      {!mobile && <span className="app-bar-title">{gameInfo?.title}</span>}
    </div>
    <div className="nav-btns">
      {mobile && <MobileNavButtons pageNumber={pageNumber} setPageNumber={setPageNumber} />}
      <MenuButton navOpen={navOpen} setNavOpen={setNavOpen} />
    </div>
    <div className={'menu dropdown' + (navOpen ? '' : ' hidden')}>
      <Button title="Game Info & Credits" inverted="true" to="" onClick={() => {toggleInfo(); setNavOpen(false)}}>
        <FontAwesomeIcon icon={faCircleInfo} />&nbsp;Game Info
      </Button>
      <Button title="Clear Progress" inverted="true" to="" onClick={() => {toggleEraseMenu(); setNavOpen(false)}}>
        <FontAwesomeIcon icon={faEraser} />&nbsp;Erase
      </Button>
      <Button title="Download Progress" inverted="true" to="" onClick={(ev) => {downloadProgress(gameId, gameProgress, ev); setNavOpen(false)}}>
        <FontAwesomeIcon icon={faDownload} />&nbsp;Download
      </Button>
      <Button title="Load Progress from JSON" inverted="true" to="" onClick={() => {toggleUploadMenu(); setNavOpen(false)}}>
        <FontAwesomeIcon icon={faUpload} />&nbsp;Upload
      </Button>
      <Button title="Impressum, privacy policy" inverted="true" to="" onClick={() => {toggleImpressum(); setNavOpen(false)}}>
        <FontAwesomeIcon icon={faCircleInfo} />&nbsp;Impressum
      </Button>
      <Button title="Preferences" inverted="true" to="" onClick={() => {togglePreferencesPopup(); setNavOpen(false)}}>
         <FontAwesomeIcon icon={faGear} />&nbsp;Preferences
       </Button>
    </div>
  </div>
}

/** the navigation bar in a level */
export function LevelAppBar({isLoading, levelTitle, toggleImpressum, pageNumber=undefined, setPageNumber=undefined} : {
  isLoading: boolean,
  levelTitle: string,
  toggleImpressum: any,
  pageNumber?: number,
  setPageNumber?: any,
}) {
  const gameId = React.useContext(GameIdContext)
  const {worldId, levelId} = React.useContext(WorldLevelIdContext)
  const {mobile} = React.useContext(PreferencesContext)
  const [navOpen, setNavOpen] = React.useState(false)
  const gameInfo = useGetGameInfoQuery({game: gameId})
  const completed = useAppSelector(selectCompleted(gameId, worldId, levelId))
  const difficulty = useAppSelector(selectDifficulty(gameId))

  let worldTitle = gameInfo.data?.worlds.nodes[worldId].title

  return <div className="app-bar" style={isLoading ? {display: "none"} : null} >
    {mobile ?
      <>
        {/* MOBILE VERSION */}
        <div>
          <span className="app-bar-title">{levelTitle}</span>
        </div>
        <div className="nav-btns">
          <InventoryButton pageNumber={pageNumber} setPageNumber={setPageNumber}/>
          <MenuButton navOpen={navOpen} setNavOpen={setNavOpen}/>
        </div>
        <div className={'menu dropdown' + (navOpen ? '' : ' hidden')}>
          <NextButton worldSize={gameInfo.data?.worldSize[worldId]} difficulty={difficulty} completed={completed} setNavOpen={setNavOpen} />
          <PreviousButton setNavOpen={setNavOpen} />
          <HomeButton isDropdown={true} />
          <InputModeButton setNavOpen={setNavOpen} isDropdown={true}/>
          <ImpressumButton setNavOpen={setNavOpen} toggleImpressum={toggleImpressum} isDropdown={true} />
          <LanguageButton setNavOpen={setNavOpen} toggleLangNav={() => {}} isDropdown={true} />
        </div>
      </> :
      <>
        {/* DESKTOP VERSION */}
        <div className='app-bar-left'>
          <HomeButton isDropdown={false} />
          <span className="app-bar-title">{worldTitle && `World: ${worldTitle}`}</span>
        </div>
        <div>
          <span className="app-bar-title">{levelTitle}</span>
        </div>
        <div className="nav-btns">
          <PreviousButton setNavOpen={setNavOpen} />
          <NextButton worldSize={gameInfo.data?.worldSize[worldId]} difficulty={difficulty} completed={completed} setNavOpen={setNavOpen} />
          <InputModeButton setNavOpen={setNavOpen} isDropdown={false}/>
          <ImpressumButton setNavOpen={setNavOpen} toggleImpressum={toggleImpressum} isDropdown={false} />
          <LanguageButton setNavOpen={setNavOpen} toggleLangNav={() => {}} isDropdown={false} />
        </div>
      </>
    }
  </div>
}
