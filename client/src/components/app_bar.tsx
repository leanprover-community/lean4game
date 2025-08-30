/**
 *  @file contains the navigation bars of the app.
 */
import * as React from 'react'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faDownload, faUpload, faEraser, faBook, faBookOpen, faGlobe, faHome,
  faArrowRight, faArrowLeft, faXmark, faBars, faCode,
  faCircleInfo, faTerminal, faGear } from '@fortawesome/free-solid-svg-icons'
import { GameIdContext } from "../app"
import { InputModeContext, PreferencesContext, WorldLevelIdContext } from "./infoview/context"
import { GameInfo, useGetGameInfoQuery } from '../state/api'
import { changedOpenedIntro, selectCompleted, selectDifficulty, selectProgress } from '../state/progress'
import { useAppDispatch, useAppSelector } from '../hooks'
import { Button } from './button'
import { downloadProgress } from './popup/erase'
import { useTranslation } from 'react-i18next'
import { useAtom } from 'jotai'
import { popupAtom, PopupType } from '../store/popup-atoms'

/** navigation buttons for mobile welcome page to switch between intro/tree/inventory. */
function MobileNavButtons({pageNumber, setPageNumber}:
  { pageNumber: number,
    setPageNumber: any}) {
  const gameId = React.useContext(GameIdContext)
  const { t } = useTranslation()
  const dispatch = useAppDispatch()

  // if `prevText` or `prevIcon` is set, show a button to go back
  let prevText  = {0: null, 1: t("Intro"), 2: null}[pageNumber]
  let prevIcon  = {0: null, 1: null, 2: faBookOpen}[pageNumber]
  let prevTitle = {0: null, 1: t("Game Introduction"), 2: t("World selection")}[pageNumber]
  // if `nextText` or `nextIcon` is set, show a button to go forward
  let nextText  = {0: t("Start"), 1: null, 2: null}[pageNumber]
  let nextIcon  = {0: null, 1: faBook, 2: null}[pageNumber]
  let nextTitle = {0: t("World selection"), 1: t("Inventory"), 2: null}[pageNumber]

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
export function MenuButton({navOpen, setNavOpen}) {
  return <Button to="" className="btn toggle-width" id="menu-btn" onClick={(ev) => {setNavOpen(!navOpen)}}>
    {navOpen ? <FontAwesomeIcon icon={faXmark} /> : <FontAwesomeIcon icon={faBars} />}
  </Button>
}

/** button to go one level futher.
 * for the last level, this button turns into a button going back to the welcome page.
 */
function NextButton({worldSize, difficulty, completed, setNavOpen}) {
  const { t } = useTranslation()
  const gameId = React.useContext(GameIdContext)
  const {worldId, levelId} = React.useContext(WorldLevelIdContext)
  return (levelId < worldSize ?
    <Button inverted="true"
        to={`/${gameId}/world/${worldId}/level/${levelId + 1}`} title={t("next level")}
        disabled={difficulty >= 2 && !(completed || levelId == 0)}
        onClick={() => setNavOpen(false)}>
      <FontAwesomeIcon icon={faArrowRight} />&nbsp;{levelId ? t("Next") : t("Start")}
    </Button>
    :
    <Button to={`/${gameId}`} inverted="true" title={t("back to world selection")} id="home-btn">
      <FontAwesomeIcon icon={faHome} />&nbsp;{t("Leave World")}
    </Button>
  )
}

/** button to go one level back.
 * only renders if the current level id is > 0.
 */
function PreviousButton({setNavOpen}) {
  const { t } = useTranslation()
  const gameId = React.useContext(GameIdContext)
  const {worldId, levelId} = React.useContext(WorldLevelIdContext)
  return (levelId > 0 && <>
    <Button disabled={levelId <= 0} inverted="true"
        to={`/${gameId}/world/${worldId}/level/${levelId - 1}`}
        title={t("previous level")}
        onClick={() => setNavOpen(false)}>
      <FontAwesomeIcon icon={faArrowLeft} />&nbsp;{t("Previous")}
    </Button>
  </>)
}

/** button to toggle between editor and typewriter */
function InputModeButton({setNavOpen, isDropdown}) {
  const { t } = useTranslation()
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
      title={lockEditorMode ? t("Editor mode is enforced!") : typewriterMode ? t("Editor mode") : t("Typewriter mode")}>
    <FontAwesomeIcon icon={(typewriterMode && !lockEditorMode) ? faCode : faTerminal} />
    {isDropdown && ((typewriterMode && !lockEditorMode) ? <>&nbsp;{t("Editor mode")}</> : <>&nbsp;{t("Typewriter mode")}</>)}
  </Button>
}

export function ImpressumButton({setNavOpen, isDropdown}) {
  const [, setPopup] = useAtom(popupAtom)

  const { t } = useTranslation()
  return <Button className="btn btn-inverted"
    title={t("Impressum")} inverted="true" to="" onClick={(ev) => {setPopup(PopupType.impressum); setNavOpen(false)}}>
    <FontAwesomeIcon icon={faCircleInfo} />
    {isDropdown && <>&nbsp;{t("Impressum")}</>}
  </Button>
}

export function PrivacyButton({setNavOpen, togglePrivacy, isDropdown}) {
  const { t } = useTranslation()
  return <Button className="btn btn-inverted"
    title={t("Privacy Policy")} inverted="true" to="" onClick={(ev) => {togglePrivacy(ev); setNavOpen(false)}}>
    <FontAwesomeIcon icon={faCircleInfo} />
    {isDropdown && <>&nbsp;{t("Privacy Policy")}</>}
  </Button>
}

export function PreferencesButton({setNavOpen, togglePreferencesPopup}) {
  const { t } = useTranslation()
  return <Button title={t("Preferences")} inverted="true" to="" onClick={() => {togglePreferencesPopup(); setNavOpen(false)}}>
    <FontAwesomeIcon icon={faGear} />&nbsp;{t("Preferences")}
  </Button>
}

function GameInfoButton({setNavOpen, toggleInfo}) {
  const { t } = useTranslation()
  return <Button className="btn btn-inverted"
    title={t("Game Info & Credits")} inverted="true" to="" onClick={() => {toggleInfo(); setNavOpen(false)}}>
    <FontAwesomeIcon icon={faCircleInfo} />&nbsp;{t("Game Info")}
  </Button>
}

function EraseButton ({setNavOpen, toggleEraseMenu}) {
  const { t } = useTranslation()
  return <Button title={t("Clear Progress")} inverted="true" to="" onClick={() => {toggleEraseMenu(); setNavOpen(false)}}>
    <FontAwesomeIcon icon={faEraser} />&nbsp;{t("Erase")}
  </Button>
}

function DownloadButton ({setNavOpen, gameId, gameProgress}) {
  const { t } = useTranslation()
  return <Button title={t("Download Progress")} inverted="true" to="" onClick={(ev) => {downloadProgress(gameId, gameProgress, ev); setNavOpen(false)}}>
    <FontAwesomeIcon icon={faDownload} />&nbsp;{t("Download")}
  </Button>
}

function UploadButton ({setNavOpen, toggleUploadMenu}) {
  const { t } = useTranslation()
  return <Button title={t("Load Progress from JSON")} inverted="true" to="" onClick={() => {toggleUploadMenu(); setNavOpen(false)}}>
    <FontAwesomeIcon icon={faUpload} />&nbsp;{t("Upload")}
  </Button>
}

/**  button to go back to welcome page */
function HomeButton({isDropdown}) {
  const { t } = useTranslation()
  const gameId = React.useContext(GameIdContext)
  return <Button to={`/${gameId}`} inverted="true" title={t("back to world selection")} id="home-btn">
    <FontAwesomeIcon icon={faHome} />
    {isDropdown && <>&nbsp;{t("Home")}</>}
  </Button>
}

function LandingPageButton() {
  const { t } = useTranslation()
  return <Button inverted="false" title={t("back to games selection")} to="/">
    <FontAwesomeIcon icon={faArrowLeft} />&nbsp;<FontAwesomeIcon icon={faGlobe} />
    </Button>
}

/** button in mobile level to toggle inventory.
 * only displays a button if `setPageNumber` is set.
 */
function InventoryButton({pageNumber, setPageNumber}) {
  const { t } = useTranslation()
  return (setPageNumber &&
    <Button to="" className="btn btn-inverted toggle-width"
      title={pageNumber ? t("close inventory") : t("show inventory")}
      inverted="true" onClick={() => {setPageNumber(pageNumber ? 0 : 1)}}>
      <FontAwesomeIcon icon={pageNumber ? faBookOpen : faBook} />
    </Button>
  )
}

/** the navigation bar on the welcome page */
export function WelcomeAppBar({pageNumber, setPageNumber, gameInfo, togglePrivacy, toggleEraseMenu, toggleUploadMenu, toggleInfo, togglePreferencesPopup} : {
  pageNumber: number,
  setPageNumber: any,
  gameInfo: GameInfo,
  togglePrivacy: any,
  toggleEraseMenu: any,
  toggleUploadMenu: any,
  toggleInfo: any,
  togglePreferencesPopup: () => void;
}) {
  const { t } = useTranslation()
  const gameId = React.useContext(GameIdContext)
  const gameProgress = useAppSelector(selectProgress(gameId))
  const {mobile} = React.useContext(PreferencesContext)
  const [navOpen, setNavOpen] = React.useState(false)

  return <div className="app-bar">
    <div className='app-bar-left'>
      <LandingPageButton />
      <span className="app-bar-title"></span>
    </div>
    <div>
      {!mobile && <span className="app-bar-title">{t(gameInfo?.title, {ns: gameId})}</span>}
    </div>
    <div className="nav-btns">
      {mobile && <MobileNavButtons pageNumber={pageNumber} setPageNumber={setPageNumber} />}
      <MenuButton navOpen={navOpen} setNavOpen={setNavOpen} />
    </div>
    <div className={'menu dropdown' + (navOpen ? '' : ' hidden')}>
      <GameInfoButton setNavOpen={setNavOpen} toggleInfo={toggleInfo}/>
      <EraseButton setNavOpen={setNavOpen} toggleEraseMenu={toggleEraseMenu}/>
      <DownloadButton setNavOpen={setNavOpen} gameId={gameId} gameProgress={gameProgress}/>
      <UploadButton setNavOpen={setNavOpen} toggleUploadMenu={toggleUploadMenu}/>
      <ImpressumButton setNavOpen={setNavOpen} isDropdown={true} />
      <PrivacyButton setNavOpen={setNavOpen} togglePrivacy={togglePrivacy} isDropdown={true} />
      <PreferencesButton setNavOpen={setNavOpen} togglePreferencesPopup={togglePreferencesPopup}/>
    </div>
  </div>
}

/** the navigation bar in a level */
export function LevelAppBar({isLoading, levelTitle, togglePrivacy, toggleInfo, togglePreferencesPopup, pageNumber=undefined, setPageNumber=undefined} : {
  isLoading: boolean,
  levelTitle: string,
  togglePrivacy: any,
  toggleInfo: any,
  togglePreferencesPopup: any,
  pageNumber?: number,
  setPageNumber?: any,
}) {
  const { t } = useTranslation()
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
          <GameInfoButton setNavOpen={setNavOpen} toggleInfo={toggleInfo}/>
          <ImpressumButton setNavOpen={setNavOpen} isDropdown={true} />
          <PrivacyButton setNavOpen={setNavOpen} togglePrivacy={togglePrivacy} isDropdown={true} />
          <PreferencesButton setNavOpen={setNavOpen} togglePreferencesPopup={togglePreferencesPopup}/>
        </div>
      </> :
      <>
        {/* DESKTOP VERSION */}
        <div className='app-bar-left'>
          <HomeButton isDropdown={false} />
          <span className="app-bar-title">{worldTitle && `${t("World")}: ${t(worldTitle, {ns: gameId})}`}</span>
        </div>
        <div>
          <span className="app-bar-title">{levelTitle}</span>
        </div>
        <div className="nav-btns">
          <PreviousButton setNavOpen={setNavOpen} />
          <NextButton worldSize={gameInfo.data?.worldSize[worldId]} difficulty={difficulty} completed={completed} setNavOpen={setNavOpen} />
          <InputModeButton setNavOpen={setNavOpen} isDropdown={false}/>
          <MenuButton navOpen={navOpen} setNavOpen={setNavOpen}/>
        </div>
        <div className={'menu dropdown' + (navOpen ? '' : ' hidden')}>
          <GameInfoButton setNavOpen={setNavOpen} toggleInfo={toggleInfo}/>
          <ImpressumButton setNavOpen={setNavOpen} isDropdown={true} />
          <PrivacyButton setNavOpen={setNavOpen} togglePrivacy={togglePrivacy} isDropdown={true} />
          <PreferencesButton setNavOpen={setNavOpen} togglePreferencesPopup={togglePreferencesPopup}/>
        </div>
      </>
    }
  </div>
}
