import {
  faBars,
  faCircleInfo,
  faDownload,
  faEraser,
  faGear,
  faHome,
  faLock,
  faLockOpen,
  faUnlock,
  faUpload,
  faXmark,
} from '@fortawesome/free-solid-svg-icons'
import { useAtom, useAtomValue, useSetAtom } from 'jotai'
import { useTranslation } from 'react-i18next'

import {
  gameIdAtom,
  gamePath,
  routeAtom,
  worldIdAtom,
} from '../state/location-atoms'
import {
  langNavOpenAtom,
  navOpenAtom,
  popupAtom,
  type PopupType,
} from '../state/navigation-atoms'
import { mobileAtom } from '../state/preferences-atoms'
import { difficultyAtom, downloadProgressAtom } from '../state/progress-atoms'
import { Dropdown } from './Dropdown'
import { ErasePopup } from './ErasePopup'
import { GameInfoPopup } from './GameInfoPopup'
import { GameNavigation } from './GameNavigation'
import { GithubIcon } from './GithubIcon'
import { LanguageButton, LanguageMenu } from './LanguageMenu'
import { NavButton } from './NavButton'
import { PageTitle, WorldTitle } from './PageTitle'
import { RulesPopup } from './RulesPopup'
import { UploadPopup } from './UploadPopup'

/** The icon of the game rules button, showing how much the current rules lock */
function rulesIcon(difficulty: number) {
  if (difficulty <= 0) return faLockOpen
  if (difficulty === 1) return faUnlock
  return faLock
}

/** The navigation bar at the top of every page */
export function AppBar() {
  const { t } = useTranslation()
  const mobile = useAtomValue(mobileAtom)
  const route = useAtomValue(routeAtom)
  const isLandingPage = route.page === 'landing'
  const [popup, setPopup] = useAtom(popupAtom)
  const closePopup = () => setPopup(null)
  const difficulty = useAtomValue(difficultyAtom)
  const [navOpen, setNavOpen] = useAtom(navOpenAtom)
  const [langNavOpen, setLangNavOpen] = useAtom(langNavOpenAtom)

  // only one of the dropdowns is open at a time
  const toggleNav = () => {
    setNavOpen(!navOpen)
    setLangNavOpen(false)
  }
  const toggleLangNav = () => {
    setLangNavOpen(!langNavOpen)
    setNavOpen(false)
  }
  const closeAll = () => {
    setNavOpen(false)
    setLangNavOpen(false)
  }
  const openPopup = (type: PopupType) => {
    closeAll()
    setPopup(type)
  }

  // only on the game overview, where the world tree depends on them
  const rulesButton = route.page === 'game' && (
    <NavButton
      icon={rulesIcon(difficulty)}
      title={t('rules.gameRules')}
      onClick={() => openPopup('rules')}
    />
  )

  const githubButton = (
    <NavButton
      iconElement={<GithubIcon />}
      title={t('appBar.github')}
      href="https://github.com/leanprover-community/lean4game"
    />
  )

  return (
    <header className="relative flex shrink-0 items-center justify-between gap-2 bg-primary px-2 py-1 text-white">
      {mobile ? (
        <>
          {/* MOBILE VERSION */}
          <div className="flex flex-1 basis-0 items-center">
            <GameNavigation />
          </div>
          <PageTitle />
          <div className="flex flex-1 basis-0 items-center justify-end">
            {isLandingPage && githubButton}
            {rulesButton}
            <LanguageButton open={langNavOpen} onToggle={toggleLangNav} />
            <NavButton
              icon={navOpen ? faXmark : faBars}
              title={navOpen ? t('appBar.closeMenu') : t('appBar.openMenu')}
              onClick={toggleNav}
            />
          </div>
          <Dropdown open={navOpen} onClose={closeAll}>
            <CommonMenuEntries onOpenPopup={openPopup} />
          </Dropdown>
        </>
      ) : (
        <>
          {/* DESKTOP VERSION */}
          <div className="flex flex-1 basis-0 items-center">
            <GameNavigation />
            <WorldTitle />
          </div>
          <PageTitle />
          <div className="flex flex-1 basis-0 items-center justify-end">
            {isLandingPage && githubButton}
            {rulesButton}
            <LanguageButton open={langNavOpen} onToggle={toggleLangNav} />
            <NavButton
              icon={navOpen ? faXmark : faBars}
              title={navOpen ? t('appBar.closeMenu') : t('appBar.openMenu')}
              onClick={toggleNav}
            />
          </div>
          <Dropdown open={navOpen} onClose={closeAll}>
            <CommonMenuEntries onOpenPopup={openPopup} />
          </Dropdown>
        </>
      )}
      <Dropdown open={langNavOpen} onClose={closeAll}>
        <LanguageMenu />
      </Dropdown>
      {'gameId' in route && (
        <>
          <GameInfoPopup open={popup === 'gameInfo'} onClose={closePopup} />
          <UploadPopup open={popup === 'upload'} onClose={closePopup} />
          <ErasePopup open={popup === 'erase'} onClose={closePopup} />
        </>
      )}
      {route.page === 'game' && (
        <RulesPopup open={popup === 'rules'} onClose={closePopup} />
      )}
    </header>
  )
}

/** The entries of the main menu which exist in both versions */
function CommonMenuEntries({
  onOpenPopup,
}: {
  onOpenPopup: (type: PopupType) => void
}) {
  const { t } = useTranslation()
  const inGame = 'gameId' in useAtomValue(routeAtom)
  const gameId = useAtomValue(gameIdAtom)
  const worldId = useAtomValue(worldIdAtom)
  const downloadProgress = useSetAtom(downloadProgressAtom)
  return (
    <>
      {/* in a world or level, back to the game overview */}
      {gameId !== undefined && worldId !== undefined && (
        <NavButton
          icon={faHome}
          text={t('appBar.home')}
          title={t('appBar.backToGame')}
          href={gamePath(gameId)}
        />
      )}
      {inGame && (
        <>
          <NavButton
            icon={faCircleInfo}
            text={t('appBar.gameInfo')}
            title={t('appBar.gameInfoTitle')}
            onClick={() => onOpenPopup('gameInfo')}
          />
          {/* the progress of this game */}
          <NavButton
            icon={faDownload}
            text={t('appBar.download')}
            title={t('appBar.downloadTitle')}
            onClick={downloadProgress}
          />
          <NavButton
            icon={faUpload}
            text={t('appBar.upload')}
            title={t('appBar.uploadTitle')}
            onClick={() => onOpenPopup('upload')}
          />
          <NavButton
            icon={faEraser}
            text={t('appBar.erase')}
            title={t('appBar.eraseTitle')}
            onClick={() => onOpenPopup('erase')}
          />
        </>
      )}
      <NavButton
        icon={faCircleInfo}
        text={t('appBar.impressum')}
        title={t('appBar.impressum')}
        href="/impressum"
      />
      <NavButton
        icon={faCircleInfo}
        text={t('appBar.privacy')}
        title={t('appBar.privacy')}
        href="/privacy"
      />
      <NavButton
        icon={faGear}
        text={t('appBar.preferences')}
        title={t('appBar.preferences')}
        href="/preferences"
      />
    </>
  )
}
