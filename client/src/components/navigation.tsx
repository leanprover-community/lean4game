import * as React from 'react'
import { createContext, useContext, useState } from 'react'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faDownload, faUpload, faEraser, faBook, faBookOpen, faGlobe, faHome,
  faArrowRight, faArrowLeft, faXmark, faBars, faCode,
  faCircleInfo, faTerminal, faGear, IconDefinition, faShield, faBug } from '@fortawesome/free-solid-svg-icons'
import { GameIdContext, PageContext, PreferencesContext } from "../state/context"
import { useGetGameInfoQuery, useLoadLevelQuery } from '../state/api'
import { downloadProgress } from './popup/erase'
import { useTranslation } from 'react-i18next'
import '../css/navigation.css'
import { PopupContext } from './popup/popup'
import { useSelector } from 'react-redux'
import { selectCompleted, selectDifficulty, selectProgress, selectReadIntro } from '../state/progress'
import lean4gameConfig from '../config.json'
import { Flag } from './flag'
import { useAppSelector } from '../hooks'

/** SVG github icon */
function GithubIcon () {
  return <svg className="svg-inline--fa" height="24" aria-hidden="true" viewBox="0 0 16 16" version="1.1" width="24" >
    <path fill="#fff" d="M8 0c4.42 0 8 3.58 8 8a8.013 8.013 0 0 1-5.45 7.59c-.4.08-.55-.17-.55-.38 0-.27.01-1.13.01-2.2 0-.75-.25-1.23-.54-1.48 1.78-.2 3.65-.88 3.65-3.95 0-.88-.31-1.59-.82-2.15.08-.2.36-1.02-.08-2.12 0 0-.67-.22-2.2.82-.64-.18-1.32-.27-2-.27-.68 0-1.36.09-2 .27-1.53-1.03-2.2-.82-2.2-.82-.44 1.1-.16 1.92-.08 2.12-.51.56-.82 1.28-.82 2.15 0 3.06 1.86 3.75 3.64 3.95-.23.2-.44.55-.51 1.07-.46.21-1.61.55-2.33-.66-.15-.24-.6-.83-1.23-.82-.67.01-.27.38.01.53.34.19.73.9.82 1.13.16.45.68 1.31 2.69.94 0 .67.01 1.3.01 1.49 0 .21-.15.45-.55.38A7.995 7.995 0 0 1 0 8c0-4.42 3.58-8 8-8Z"></path>
  </svg>
}

/** A button to appear in the navigation (both, top bar or dropdown). */
export const NavButton: React.FC<{
  icon?: IconDefinition
  iconElement?: JSX.Element
  text?: string
  onClick?: React.MouseEventHandler<HTMLAnchorElement>
  title?: string
  href?: string
  inverted?: boolean
  disabled?: boolean
  className?: string
}> = ({icon, iconElement, text, onClick=()=>{}, title, href=null, inverted=false, disabled=false, className=''}) => {
  return <a className={`${className} nav-button btn${inverted?' btn-inverted':''}${disabled?' btn-disabled':''}`} onClick={disabled?null:onClick} href={disabled?null:href} title={title}>
    {iconElement ?? (icon && <FontAwesomeIcon icon={icon} />)}{text && <>&nbsp;{text}</>}
  </a>
}

/** Context which manages the dropdown navigation */
const NavigationContext = createContext<{
  navOpen: boolean,
  setNavOpen: React.Dispatch<React.SetStateAction<boolean>>
}>({navOpen: false, setNavOpen: () => {}})

/** Content of the navigation during game selection. */
function NavigationLandingPage () {
  return <div className="nav-content">
    <div className="nav-title-left"></div>
    <div className="nav-title-middle"></div>
    <div className="nav-title-right"></div>
  </div>
}

/** Content of the navigation on Desktop during world selection. */
function DesktopNavigationOverview () {
  const { t } = useTranslation()
  const { gameId } = useContext(GameIdContext)
  const { setPopupContent } = useContext(PopupContext)
  const gameInfo = useGetGameInfoQuery({game: gameId})

  return <div className="nav-content">
    <div className="nav-title-left">
      <NavButton
        text={t("Rules")}
        onClick={() => {setPopupContent("rules")}}
        inverted={true} />
    </div>
    <div className="nav-title-middle">
      <span className="nav-title">{t(gameInfo.data?.title, {ns: gameId})}</span>
    </div>
    <div className="nav-title-right"></div>
  </div>
}

/** Content of the navigation on Mobile during world selection. */
function MobileNavigationOverview () {
  const { t } = useTranslation()
  const {page, setPage} = useContext(PageContext)
  const { setPopupContent } = useContext(PopupContext)

  const { gameId, worldId } = useContext(GameIdContext)
  const readIntro = useSelector(selectReadIntro(gameId, worldId))

  return <div className="nav-content">
    <div className="nav-title-left">
      <NavButton
        text={t("Rules")}
        onClick={() => {setPopupContent("rules")}}
        inverted={true} />
    </div>
    <div className="nav-title-middle">
      <span className="nav-title">
      </span>
    </div>
    <div className="nav-title-right">
      {page > 0 &&
        <NavButton
        text={page == 1 ? t("Intro") : null}
        icon={page == 1 ? null : faBookOpen}
        onClick={() => setPage(page - 1)}
          inverted={true} />
      }
      { page < 2 &&
        <NavButton
          text={(page==0) ? t("Start") : null}
          icon={(page==0) ? null : faBook}
          onClick={() => setPage(page+1)}
          disabled={!readIntro}
          inverted={true} />
      }
    </div>

  </div>
}

/** Content of the navigation on Desktop in a level. */
function DesktopNavigationLevel () {
  const { t } = useTranslation()
  const { gameId, worldId, levelId } = useContext(GameIdContext)
  const { typewriterMode, setTypewriterMode, lockEditorMode } = useContext(PageContext)
  const gameInfo = useGetGameInfoQuery({game: gameId})
  const levelInfo = useLoadLevelQuery({game: gameId, world: worldId, level: levelId})
  const difficulty = useSelector(selectDifficulty(gameId))
  const completed = useAppSelector(selectCompleted(gameId, worldId, levelId))

  const readIntro = useSelector(selectReadIntro(gameId, worldId))

  const worldTitle = gameInfo.data?.worlds.nodes[worldId]?.title
  const levelTitle = ((levelId == 0) ?
    t("Introduction") :
    (
      t("Level") +
      ` ${levelId}` +
      (gameInfo.data?.worldSize[worldId] ? ` / ${gameInfo.data?.worldSize[worldId]}` : '') +
      (levelInfo.data?.title ? ` : ${t(levelInfo?.data?.title, {ns: gameId})}` : '')
    )
  )

  return <div className="nav-content">
    <div className="nav-title-left">
    <span className="nav-title">{worldTitle ? `${t(worldTitle, {ns: gameId})}` : '' /* ${t("World")}: */ }
    </span>
    </div>
    <div className="nav-title-middle">
      <span className="nav-title">
        { levelTitle
        }
      </span>
    </div>
    <div className="nav-title-right" >
      { levelId > 0 &&
        <NavButton
          icon={faArrowLeft}
          text={t("Previous")}
          inverted={true}
          href={`#/${gameId}/world/${worldId}/level/${levelId - 1}`} />
      }
      { levelId == gameInfo.data?.worldSize[worldId] ?
        <NavButton
          icon={faHome}
          text={t("Home")}
          inverted={true}
          disabled={levelId > 0 && difficulty == 2 && !completed}
          href={`#/${gameId}`} /> :
        <NavButton
          icon={faArrowRight}
          text={levelId == 0 ? t("Start") : t("Next")} inverted={true}
          disabled={levelId == 0 ? !readIntro : (difficulty == 2 && !completed)}
          href={`#/${gameId}/world/${worldId}/level/${levelId + 1}`} />
      }
    </div>
  </div>
}

/** Content of the navigation on Mobile in a level. */
function MobileNavigationLevel () {
  const { t } = useTranslation()
  const {gameId, worldId, levelId} = useContext(GameIdContext)
  const {page, setPage} = useContext(PageContext)
  const gameInfo = useGetGameInfoQuery({game: gameId})
  const levelInfo = useLoadLevelQuery({game: gameId, world: worldId, level: levelId})

  let title = worldId ?
    ` ${levelId} / ${gameInfo.data?.worldSize[worldId]}`+ (levelInfo?.data?.title && ` : ${t(levelInfo?.data?.title, {ns: gameId})}`)
    :
    ''

  return <div className="nav-content">
    <div className="nav-title-left"></div>
    <div className="nav-title-middle">
      <span className="nav-title">
        {title}
      </span>
    </div>
    <div className="nav-title-right">
      <NavButton
        icon={(page == 1) ? faBook : faBookOpen}
        onClick={() => setPage((page == 1) ? 2 : 1)}
        inverted={true} />
    </div>
  </div>
}

/** The skeleton of the navigation which is the same across all layouts. */
export function Navigation () {
  const { t, i18n } = useTranslation()
  const { gameId, worldId, levelId } = useContext(GameIdContext)
  const { mobile, language, setLanguage } = useContext(PreferencesContext)
  const { setPopupContent } = useContext(PopupContext)
  const { typewriterMode, setTypewriterMode, lockEditorMode } = useContext(PageContext)
  const gameProgress = useSelector(selectProgress(gameId))
  const gameInfo = useGetGameInfoQuery({game: gameId})
  const levelInfo = useLoadLevelQuery({game: gameId, world: worldId, level: levelId})
  const difficulty = useSelector(selectDifficulty(gameId))
  const completed = useAppSelector(selectCompleted(gameId, worldId, levelId))

  const readIntro = useSelector(selectReadIntro(gameId, worldId))

  const [navOpen, setNavOpen] = useState(false)
  const [langNavOpen, setLangNavOpen] = useState(false)
  function toggleNav () {setNavOpen(!navOpen); setLangNavOpen(false)}
  function toggleLangNav () {setLangNavOpen(!langNavOpen); setNavOpen(false)}

  /** toggle input mode if allowed */
  function toggleInputMode(ev: React.MouseEvent) {
    if (!lockEditorMode) {
      setTypewriterMode(!typewriterMode)
      console.log('test')
    }
  }

  return <nav>
    <NavigationContext.Provider value={{navOpen, setNavOpen}}>
      { gameId && <>
        <NavButton
          icon={worldId ? faHome : faGlobe}
          title={worldId ? t("home") : t("back to games selection")}
          href={worldId ? `#/${gameId}` : `#`} />
      </>}
      { gameId ?
        worldId ?
          (mobile ? <MobileNavigationLevel /> : <DesktopNavigationLevel />) :
          (mobile ? <MobileNavigationOverview /> : <DesktopNavigationOverview />) :
        <NavigationLandingPage />
      }
      { !gameId &&
        <NavButton
          iconElement={<GithubIcon />}
          title={t("view the Lean game server on Github")}
          href='https://github.com/leanprover-community/lean4game' />
      }
      {(!gameId || gameInfo.data?.tile?.languages.length > 1) &&
        // Language button only visible if the game exists in `>1` languages
        <NavButton
          iconElement={langNavOpen ? null : <Flag iso={i18n.language} />}
          icon={langNavOpen ? faXmark : null}
          title={langNavOpen ? t('close language menu') : t('open language menu')}
          onClick={toggleLangNav}
          />
      }
      <NavButton
        icon={navOpen ? faXmark : faBars}
        title={navOpen ? t('close menu') : t('open menu')}
        onClick={toggleNav} />
      { langNavOpen &&
        <div className='dropdown' onClick={toggleLangNav} >
          {gameId && gameInfo.data?.tile?.languages ?
            // Show all languages the game is available in
            gameInfo.data?.tile?.languages.map(iso =>
              <NavButton
                key={`lang-selection-${iso}`}
                iconElement={<Flag iso={iso} />}
                text={lean4gameConfig.newLanguages[iso]?.name}
                onClick={() => {setLanguage(iso)}}
                inverted={true} />) :
            // Show all languages the interface is available in (e.g. landing page)
            Object.entries(lean4gameConfig.newLanguages).map(([iso, val]) =>
              <NavButton
                key={`lang-selection-${iso}`}
                iconElement={<Flag iso={iso} />}
                text={lean4gameConfig.newLanguages[iso]?.name}
                onClick={() => {setLanguage(iso)}}
                inverted={true} />)
          }
        </div>
      }
      { navOpen &&
        <div className='dropdown' onClick={toggleNav} >
          { gameId && <>
            { mobile && (levelId == gameInfo.data?.worldSize[worldId] ?
              <NavButton
                icon={faHome}
                text={t("Home")}
                inverted={true}
                disabled={levelId > 0 && difficulty == 2 && !completed}
                href={`#/${gameId}`} /> :
              <NavButton
                icon={faArrowRight}
                text={levelId == 0 ? t("Start") : t("Next")} inverted={true}
                disabled={levelId == 0 ? !readIntro : (difficulty == 2 && !completed)}
                href={`#/${gameId}/world/${worldId}/level/${levelId + 1}`} />
            )}
            {mobile && levelId > 0 &&
              <NavButton
                icon={faArrowLeft}
                text={t("Previous")}
                inverted={true}
                href={`#/${gameId}/world/${worldId}/level/${levelId - 1}`} />
            }
            { mobile && levelId > 0 &&
              <NavButton
                icon={(typewriterMode && !lockEditorMode) ? faCode : faTerminal}
                inverted={true}
                text={typewriterMode ? t("Editor Mode") : t("Typewriter Mode")}
                disabled={levelId == 0 || lockEditorMode}
                onClick={(ev) => toggleInputMode(ev)}
                title={lockEditorMode ? t("Editor mode is enforced!") : typewriterMode ? t("Editor mode") : t("Typewriter mode")} />
            }
            <NavButton
              icon={faCircleInfo}
              text={t("Game Info")}
              onClick={() => {setPopupContent("info")}}
              inverted={true} />
            <NavButton
              icon={faEraser}
              text={t("Erase")}
              onClick={() => {setPopupContent("erase")}}
              inverted={true} />
            <NavButton
              icon={faDownload}
              text={t("Download")}
              onClick={() => {downloadProgress(gameId, gameProgress)}}
              inverted={true} />
            <NavButton
              icon={faUpload}
              text={t("Upload")}
              onClick={() => {setPopupContent("upload")}}
              inverted={true} />
			<NavButton
              icon={faBug}
              text={t("Report Problem")}
              onClick={() => {setPopupContent("report_problem")}}
              inverted={true} />
          </>}
          <NavButton
            icon={faCircleInfo}
            text={t("Impressum")}
            onClick={() => {setPopupContent("impressum")}}
            inverted={true} />
          <NavButton
            icon={faShield}
            text={t("Privacy Policy")}
            onClick={() => {setPopupContent("privacy")}}
            inverted={true} />
          <NavButton
            icon={faGear}
            text={t("Preferences")}
            onClick={() => {setPopupContent("preferences")}}
            inverted={true} />
        </div>
      }
    </NavigationContext.Provider>
  </nav>
}
