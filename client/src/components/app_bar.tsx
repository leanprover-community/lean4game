/**
 *  @file contains the navigation bars of the app.
 */
import * as React from 'react'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faDownload, faUpload, faEraser, faBook, faBookOpen, faGlobe, faHome,
  faArrowRight, faArrowLeft, faXmark, faBars, faCode,
  faCircleInfo, faTerminal, faGear } from '@fortawesome/free-solid-svg-icons'
import { Button } from './button'
import { downloadProgress } from './popup/erase'
import { useTranslation } from 'react-i18next'
import { useAtom } from 'jotai'
import { popupAtom, PopupType } from '../store/popup-atoms'
import { closeNavAtom, navOpenAtom } from '../store/navigation-atoms'
import { useGameTranslation } from '../utils/translation'
import { gameIdAtom, levelIdAtom, navigateToLandingPageAtom, worldIdAtom } from '../store/location-atoms'
import { completedAtom, difficultyAtom, progressAtom } from '../store/progress-atoms'
import { gameInfoAtom } from '../store/query-atoms'
import { readGameIntroAtom } from '../store/chat-atoms'
import { lockEditorModeAtom, typewriterModeAtom } from '../store/editor-atoms'
import { mobileAtom } from '../store/preferences-atoms'

/** navigation buttons for mobile welcome page to switch between intro/tree/inventory. */
function MobileNavButtons({pageNumber, setPageNumber}:
  { pageNumber: number,
    setPageNumber: any}) {
  const { t } = useTranslation()
  const [, navigateToLandingPage] = useAtom(navigateToLandingPageAtom)
  const [, setReadGameIntro] = useAtom(readGameIntroAtom)

  // if `prevText` or `prevIcon` is set, show a button to go back
  let prevText  = {0: null, 1: t("Intro"), 2: null}[pageNumber]
  let prevIcon  = {0: null, 1: null, 2: faBookOpen}[pageNumber]
  let prevTitle = {0: null, 1: t("Game Introduction"), 2: t("close inventory")}[pageNumber] ?? undefined
  // if `nextText` or `nextIcon` is set, show a button to go forward
  let nextText  = {0: t("Start"), 1: null, 2: null}[pageNumber]
  let nextIcon  = {0: null, 1: faBook, 2: null}[pageNumber]
  let nextTitle = {0: t("Start"), 1: t("Inventory"), 2: null}[pageNumber] ?? undefined

  return <>
    {(prevText || prevIcon) &&
      <Button
        className="btn btn-inverted toggle-width"
        onClick={() => {pageNumber == 0 ? navigateToLandingPage() : setPageNumber(pageNumber - 1)}}
        inverted={true} title={prevTitle}>
          {prevIcon && <FontAwesomeIcon icon={prevIcon} />}
          {prevText && `${prevText}`}
      </Button>
    }
    {(nextText || nextIcon) &&
      <Button className="btn btn-inverted toggle-width"  inverted={true}
          title={nextTitle}
          onClick={() => {
            console.log(`page number: ${pageNumber}`)
            setPageNumber(pageNumber+1);
            setReadGameIntro(true)
          }}
      >
        {nextText && `${nextText}`}
        {nextIcon && <FontAwesomeIcon icon={nextIcon} />}
      </Button>
    }
  </>
}

/** button to toggle dropdown menu. */
export function MenuButton() {
  const [navOpen, setNavOpen] = useAtom(navOpenAtom)
  return <Button  className="btn toggle-width" id="menu-btn" onClick={(ev) => {setNavOpen(!navOpen)}}>
    {navOpen ? <FontAwesomeIcon icon={faXmark} /> : <FontAwesomeIcon icon={faBars} />}
  </Button>
}

/**
 * button to go one level futher.
 * for the last level, this button turns into a button going back to the welcome page.
 */
function NextButton({worldSize} : {worldSize: number }) {
  const [, closeNav] = useAtom(closeNavAtom)
  const { t } = useTranslation()
  const [gameId, navigateToGame] = useAtom(gameIdAtom)
  const [levelId, navigateToLevel] = useAtom(levelIdAtom)
  const [difficulty] = useAtom(difficultyAtom)
  const [completed] = useAtom(completedAtom)
  if (levelId === undefined) return null
  if (levelId == 0) return (
    <Button inverted={true}
        onClick={() => {navigateToLevel(levelId + 1); closeNav()}}
         title={t("next level")}
      >
      <FontAwesomeIcon icon={faArrowRight} />&nbsp;{t("Start")}
    </Button>
  )
  if (levelId < worldSize) return (
    <Button inverted={true}
        onClick={() => {navigateToLevel(levelId + 1); closeNav()}}
        title={t("next level")}
        disabled={difficulty >= 2 && !(completed || levelId === 0)}
      >
      <FontAwesomeIcon icon={faArrowRight} />&nbsp;{t("Next")}
    </Button>
  )
  return (
    <Button onClick={() => {if (gameId) navigateToGame(gameId)}}  inverted={true} title={t("Home")} id="home-btn">
      <FontAwesomeIcon icon={faHome} />&nbsp;{t("Home")}
    </Button>
  )
}

/** button to go one level back.
 * only renders if the current level id is > 0.
 */
function PreviousButton() {
  const [, closeNav] = useAtom(closeNavAtom)
  const { t } = useTranslation()
  const [gameId] = useAtom(gameIdAtom)
  const [worldId] = useAtom(worldIdAtom)
  const [levelId, navigateToLevel] = useAtom(levelIdAtom)
  if (!levelId) return null
  return (
    <Button disabled={levelId <= 0} inverted={true}
        onClick={() => {navigateToLevel(levelId - 1); closeNav()}}
        title={t("previous level")}
      >
      <FontAwesomeIcon icon={faArrowLeft} />&nbsp;{t("Previous")}
    </Button>
  )
}

/** button to toggle between editor and typewriter */
function InputModeButton({ isDropdown } : {isDropdown: boolean}) {
  const [, closeNav] = useAtom(closeNavAtom)
  const { t } = useTranslation()
  const [levelId] = useAtom(levelIdAtom)
  const [typewriterMode, setTypewriterMode] = useAtom(typewriterModeAtom)
  const [lockEditorMode] = useAtom(lockEditorModeAtom)

  /** toggle input mode if allowed */
  function toggleInputMode(ev: React.MouseEvent) {
    if (!lockEditorMode){
      setTypewriterMode(!typewriterMode)
      closeNav()
    }
  }

  return <Button
      className={`btn btn-inverted ${isDropdown? '' : 'toggle-width'}`} disabled={!levelId || levelId <= 0 || lockEditorMode}
      inverted={true}
      onClick={(ev) => toggleInputMode(ev)}
      title={lockEditorMode ? t("Editor mode is enforced!") : typewriterMode ? t("Editor mode") : t("Typewriter mode")}>
    <FontAwesomeIcon icon={(typewriterMode && !lockEditorMode) ? faCode : faTerminal} />
    {isDropdown && ((typewriterMode && !lockEditorMode) ? <>&nbsp;{t("Editor mode")}</> : <>&nbsp;{t("Typewriter mode")}</>)}
  </Button>
}

export function ImpressumButton({ isDropdown } : {isDropdown: boolean}) {
  const [, closeNav] = useAtom(closeNavAtom)
  const [, setPopup] = useAtom(popupAtom)
  const { t } = useTranslation()
  return <Button className="btn btn-inverted"
    title={t("Impressum")} inverted={true}  onClick={(ev) => {setPopup(PopupType.impressum); closeNav()}}>
    <FontAwesomeIcon icon={faCircleInfo} />
    {isDropdown && <>&nbsp;{t("Impressum")}</>}
  </Button>
}

export function PrivacyButton({ isDropdown } : {isDropdown: boolean}) {
  const [, closeNav] = useAtom(closeNavAtom)
  const [, setPopup] = useAtom(popupAtom)
  const { t } = useTranslation()
  return <Button className="btn btn-inverted"
    title={t("Privacy Policy")} inverted={true} onClick={(ev) => {setPopup(PopupType.privacy); closeNav()}}>
    <FontAwesomeIcon icon={faCircleInfo} />
    {isDropdown && <>&nbsp;{t("Privacy Policy")}</>}
  </Button>
}

export function PreferencesButton() {
  const [, closeNav] = useAtom(closeNavAtom)
  const [, setPopup] = useAtom(popupAtom)
  const { t } = useTranslation()
  return <Button title={t("Preferences")} inverted={true}  onClick={() => {setPopup(PopupType.preferences); closeNav()}}>
    <FontAwesomeIcon icon={faGear} />&nbsp;{t("Preferences")}
  </Button>
}

function GameInfoButton() {
  const [, closeNav] = useAtom(closeNavAtom)
  const [, setPopup] = useAtom(popupAtom)
  const { t } = useTranslation()
  return <Button className="btn btn-inverted"
    title={t("Game Info & Credits")} inverted={true}  onClick={() => {setPopup(PopupType.info); closeNav()}}>
    <FontAwesomeIcon icon={faCircleInfo} />&nbsp;{t("Game Info")}
  </Button>
}

function EraseButton () {
  const [, closeNav] = useAtom(closeNavAtom)
  const [, setPopup] = useAtom(popupAtom)
  const { t } = useTranslation()
  return <Button title={t("Clear Progress")} inverted={true}  onClick={() => {setPopup(PopupType.erase); closeNav()}}>
    <FontAwesomeIcon icon={faEraser} />&nbsp;{t("Erase")}
  </Button>
}

function DownloadButton () {
  const [, closeNav] = useAtom(closeNavAtom)
  const [gameId] = useAtom(gameIdAtom)
  const [gameProgress] = useAtom(progressAtom)
  const { t } = useTranslation()
  return <Button
    title={t("Download Progress")}
    inverted={true}
    disabled={!gameId}
    onClick={(ev) => {
      ev.preventDefault()
      if (gameId && gameProgress) {
        downloadProgress(gameId, gameProgress)
      }
      closeNav()
    }}
  >
    <FontAwesomeIcon icon={faDownload} />&nbsp;{t("Download")}
  </Button>
}

function UploadButton () {
  const [, closeNav] = useAtom(closeNavAtom)
  const [, setPopup] = useAtom(popupAtom)
  const { t } = useTranslation()
  return <Button title={t("Load Progress from JSON")} inverted={true}  onClick={() => {setPopup(PopupType.upload); closeNav()}}>
    <FontAwesomeIcon icon={faUpload} />&nbsp;{t("Upload")}
  </Button>
}

/**  button to go back to welcome page */
function HomeButton({ isDropdown } : {isDropdown: boolean}) {
  const { t } = useTranslation()
  const [gameId, navigateToGame] = useAtom(gameIdAtom)
  return <Button
    onClick={() => {if (gameId) navigateToGame(gameId)}}
    inverted={true} title={t("Home")} id="home-btn">
    <FontAwesomeIcon icon={faHome} />
    {isDropdown && <>&nbsp;{t("Home")}</>}
  </Button>
}

function LandingPageButton() {
  const { t } = useTranslation()
  const [, navigateToLandingPage] = useAtom(navigateToLandingPageAtom)
  return <Button inverted={false} title={t("back to games selection")} onClick={() => navigateToLandingPage()}>
    <FontAwesomeIcon icon={faArrowLeft} />&nbsp;<FontAwesomeIcon icon={faGlobe} />
    </Button>
}

/** button in mobile level to toggle inventory.
 * only displays a button if `setPageNumber` is set.
 */
function InventoryButton({pageNumber, setPageNumber} : {pageNumber: number, setPageNumber: (val: number) => void}) {
  const { t } = useTranslation()
  return (setPageNumber &&
    <Button  className="btn btn-inverted toggle-width"
      title={pageNumber ? t("close inventory") : t("show inventory")}
      inverted={true} onClick={() => {setPageNumber(pageNumber ? 0 : 1)}}>
      <FontAwesomeIcon icon={pageNumber ? faBookOpen : faBook} />
    </Button>
  )
}

/** the navigation bar on the welcome page */
export function WelcomeAppBar({pageNumber, setPageNumber} : {
  pageNumber: number,
  setPageNumber: any,
}) {
  const { t } = useTranslation()
  const { t: gT } = useGameTranslation()
  const [{data: gameInfo}] = useAtom(gameInfoAtom)
  const [mobile] = useAtom(mobileAtom)
  const [navOpen, setNavOpen] = useAtom(navOpenAtom)

  return <div className="app-bar">
    <div className='app-bar-left'>
      <LandingPageButton />
      <span className="app-bar-title"></span>
    </div>
    <div>
      {!mobile && <span className="app-bar-title">{gT(gameInfo?.title ?? "")}</span>}
    </div>
    <div className="nav-btns">
      {mobile && <MobileNavButtons pageNumber={pageNumber} setPageNumber={setPageNumber} />}
      <MenuButton />
    </div>
    <div className={'menu dropdown' + (navOpen ? '' : ' hidden')}>
      <GameInfoButton />
      <EraseButton />
      <DownloadButton />
      <UploadButton />
      <ImpressumButton isDropdown={true} />
      <PrivacyButton isDropdown={true} />
      <EraseButton />
      <PreferencesButton />
    </div>
  </div>
}

/** the navigation bar in a level */
export function LevelAppBar({isLoading, levelTitle, pageNumber=1, setPageNumber=undefined} : {
  isLoading: boolean,
  levelTitle: string,
  pageNumber?: number,
  setPageNumber?: any,
}) {
  const { t } = useTranslation()
  const { t: gT } = useGameTranslation()
  const [gameId] = useAtom(gameIdAtom)
  const [worldId] = useAtom(worldIdAtom)
  const [mobile] = useAtom(mobileAtom)
  const [navOpen, setNavOpen] = useAtom(navOpenAtom)
  const [{data: gameInfo}] = useAtom(gameInfoAtom)


  let worldTitle = worldId ? gameInfo?.worlds?.nodes[worldId]?.title : ""

  return <div className="app-bar" style={isLoading ? {display: "none"} : undefined} >
    {mobile ?
      <>
        {/* MOBILE VERSION */}
        <div>
          <span className="app-bar-title">{levelTitle}</span>
        </div>
        <div className="nav-btns">
          <InventoryButton pageNumber={pageNumber} setPageNumber={setPageNumber}/>
          <MenuButton />
        </div>
        <div className={'menu dropdown' + (navOpen ? '' : ' hidden')}>
          <NextButton worldSize={gameInfo?.worldSize?.[worldId]} />
          <PreviousButton />
          <HomeButton isDropdown={true} />
          <InputModeButton isDropdown={true}/>
          <GameInfoButton />
          <ImpressumButton isDropdown={true} />
          <PrivacyButton isDropdown={true} />
          <EraseButton />
          <PreferencesButton />
        </div>
      </> :
      <>
        {/* DESKTOP VERSION */}
        <div className='app-bar-left'>
          <HomeButton isDropdown={false} />
          <span className="app-bar-title">{worldTitle && gT(worldTitle)}</span>
        </div>
        <div>
          <span className="app-bar-title">{levelTitle}</span>
        </div>
        <div className="nav-btns">
          <PreviousButton  />
          <NextButton worldSize={gameInfo?.worldSize?.[worldId]} />
          <InputModeButton isDropdown={false}/>
          <MenuButton  />
        </div>
        <div className={'menu dropdown' + (navOpen ? '' : ' hidden')}>
          <GameInfoButton />
          <ImpressumButton isDropdown={true} />
          <PrivacyButton isDropdown={true} />
          <EraseButton />
          <PreferencesButton />
        </div>
      </>
    }
  </div>
}
