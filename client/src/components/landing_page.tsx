import * as React from 'react';
import { Trans, useTranslation } from 'react-i18next';
import '@fontsource/roboto/300.css';
import '@fontsource/roboto/400.css';
import '@fontsource/roboto/500.css';
import '@fontsource/roboto/700.css';
import '../css/landing_page.css'
import bgImage from '../assets/bg.jpg'
import { Markdown } from './markdown';
import path from 'path';
import { ImpressumButton, LanguageButton, LanguageDropdown, MenuButton, PreferencesButton, PrivacyButton } from './app_bar';
import ReactCountryFlag from 'react-country-flag';
import lean4gameConfig from '../config.json'
import i18next from 'i18next';
import { popupAtom, PopupType } from '../store/popup-atoms';
import { useAtom } from 'jotai';
import { GithubIcon } from './navigation/github_icon';
import { navOpenAtom } from '../store/navigation-atoms';
import { gameIdAtom } from '../store/location-atoms';
import { gameInfoAtomFamily } from '../store/query-atoms';
import { preferencesAtom } from '../store/preferences-atoms';
import { gameTilesAtom } from '../store/tiles-atoms';
import { GameTileWithName } from '../store/api';

function Tile({tileWithName}: {tileWithName: GameTileWithName}) {
  const { t, i18n } = useTranslation()
  const [, navigateToGame] = useAtom(gameIdAtom)
  const [preferences] = useAtom(preferencesAtom)

  const gameTile = tileWithName.tile
  const gameId = `g/${tileWithName.owner}/${tileWithName.game}`

  return <div className="game" onClick={() => navigateToGame(gameId)}>
      <div className="wrapper">
        <div className="title">{t(gameTile.title, {ns: gameId})}</div>
        <div className="short-description">{t(gameTile.short, { ns: gameId })}
        </div>
        { gameTile.image ? <img className="image" src={path.join("data", gameId, gameTile.image)} alt="" /> : <div className="image"/> }
        <div className="long description"><Markdown>{t(gameTile.long, { ns: gameId })}</Markdown></div>
      </div>
      <table className="info">
        <tbody>
        <tr>
          <td title="consider playing these games first.">{t("Prerequisites")}</td>
          <td><Markdown>{t(gameTile.prerequisites.join(', '), { ns: gameId })}</Markdown></td>
        </tr>
        <tr>
          <td>{t("Worlds")}</td>
          <td>{gameTile.worlds}</td>
        </tr>
        <tr>
          <td>{t("Levels")}</td>
          <td>{gameTile.levels}</td>
        </tr>
        <tr className="languages">
          <td>{t("Language")}</td>

          <td>
            {gameTile.languages.map((lang) => {
              let langOpt = lean4gameConfig.languages.find((e) => e.iso == lang)
              if (preferences.useFlags && langOpt?.flag) {
                return <ReactCountryFlag key={`flag-${lang}`} title={langOpt.name} countryCode={langOpt.flag} className="emojiFlag"/>
              } else {
                return <span key={`iso-${lang}`} title={langOpt?.name}>{lang}</span>
              }
            })}
          </td>
        </tr>
        </tbody>
      </table>
  </div>
}


function LandingPage() {
  const [, setPopup] = useAtom(popupAtom)
  const [navOpen] = useAtom(navOpenAtom)
  const [tiles] = useAtom(gameTilesAtom)

  const [usageCPU, setUsageCPU] = React.useState<number>()
  const [usageMem, setUsageMem] = React.useState<number>()
  const showUsageMem = usageMem !== undefined && usageMem >= 0
  const showUsageCPU = usageCPU !== undefined && usageCPU >= 0

  const { t, i18n } = useTranslation()

  // Load the namespaces of all games
  i18n.loadNamespaces(tiles.map(tileWithName => `g/${tileWithName.owner}/${tileWithName.game}`))

  /** Parse `games/stats.csv` if present and display server capacity. */
  React.useEffect(() => {
    const interval = setInterval(() => {
      fetch_stats();
    }, 2000)
    return () => clearInterval(interval)
  }, [])

  return <div className="landing-page">
    <header style={{backgroundImage: `url(${bgImage})`}}>
      <nav className="landing-page-nav">
        <LanguageButton />
        <GithubIcon url="https://github.com/leanprover-community/lean4game"/>
        <MenuButton />
        <LanguageDropdown />
        <div className={'menu dropdown' + (navOpen ? '' : ' hidden')}>
            <ImpressumButton isDropdown={true} />
            <PrivacyButton isDropdown={true} />
            <PreferencesButton />
        </div>
      </nav>
      <div id="main-title">
        <h1>{t("Caption.translation", { defaultValue: "Lean Game Server"})}</h1>
        <p>
          <Trans
            i18nKey="Subcaption.description"
            defaults="A repository of learning games for the proof assistant <1>Lean</1> <i>(Lean 4)</i> and its mathematical library <2>mathlib</2>"
            components={
              {1: <a target="_blank" href="https://leanprover-community.github.io/"/>,
               2: <a target="_blank" href="https://github.com/leanprover-community/mathlib4"/>
            }}
          />
        </p>
      </div>
    </header>
    <div className="game-list">
      {
      tiles.map((tileWithName, i) => {
          return <Tile
            key={tileWithName.owner + tileWithName.game}
            tileWithName={tileWithName}
          />
        })
      }
      {/* {allTiles.filter(x => x != null).length == 0 ?
        <p>
          <Trans
            i18nKey="No Games.description"
            default="No Games loaded. Use <1>http://localhost:3000/#/g/local/FOLDER</1> to open a game directly from a local folder."
            components={{1: <a />}}
          />
        </p>
        : lean4gameConfig.allGames.map((id, i) => (
          <Tile
            key={id}
            gameId={`g/${id}`}
          />
        ))
      } */}
    </div>
    { // show server capacity from `games/stats.csv` if present
      (showUsageMem || showUsageCPU) &&
      <section>
        <div className="wrapper">
          <h2>{t("Server capacity.translation", { defaultValue: "Server capacity" })}</h2>
          <Trans
            i18nKey="Server capacity.description"
            defaults="<p>As this server runs lean on our university machines, it has a limited capacity. We estimate that our setup will support around 50 simultaneous games at high performance, and up to 180 simultaneous games at a slower pace.</p>"
          />
          <p>
            { showUsageMem && <> {t("RAM")}: <strong>{usageMem.toFixed(2)} %</strong>{t(" used")}.<br/></> }
            { showUsageCPU && <> {t("CPU")}: <strong>{usageCPU.toFixed(2)} %</strong>{t(" used")}. </> }
          </p>
        </div>
      </section>
    }
    <section>
      <div className="wrapper">
        <h2>{t("Development notes.translation", { defaultValue: "Development notes" })}</h2>
        <Trans
          i18nKey="Development notes.description"
          defaults="<p>Most aspects of the games and the infrastructure are still in development. Feel free to file a <1>GitHub Issue</1> about any problems you experience!</p>"
          components={{1: <a target="_blank" href="https://github.com/leanprover-community/lean4game/issues"/>}}
        />
      </div>
    </section>
    <section>
      <div className="wrapper">
        <h2>{t("Adding new games.translation", { defaultValue: "Adding new games" })}</h2>
        <Trans
          i18nKey="Adding new games.description"
          defaults="If you are considering writing your own game, you should use the <1>GameSkeleton Github Repo</1> as a template and read <2>How to Create a Game</2>.<p>You can directly load your games into the server and play it using the correct URL. The <3>instructions above</3> also explain the details for how to load your game to the server. We'd like to encourage you to contact us if you have any questions.</p><p>Featured games on this page are added manually. Please get in contact and we'll happily add yours.</p>"
          components={
            {
             1: <a target="_blank" href="https://github.com/hhu-adam/GameSkeleton"/>,
             2: <a target="_blank" href="https://github.com/leanprover-community/lean4game/"/>,
             3: <a target="_blank" href="https://github.com/leanprover-community/lean4game/"/>,
            }
          }
        />
      </div>
    </section>
    <section>
      <div className="wrapper">
        {/* "Funding.translation" is a key corresponding to a .json entry in a translation.json file. */}
        <h2>{t("Funding.translation", { defaultValue: "Funding" })}</h2>
        <p>
          <Trans
            i18nKey="Funding.description"
            defaults="This server is hosted at Heinrich Heine University Düsseldorf. The lean4game software was developed as part of the project <1>ADAM: Anticipating the Digital Age of Mathematics</1>, funded by the programme <i>Freiraum 2022</i> of the <i>Stiftung Innovation in der Hochschullehre</i>. Ongoing maintenance and development are generously supported by <i>Renaissance Philanthropy</i> through the <i>AI for Math Fund</i>."
            components={{1: <a target="_blank" href="https://hhu-adam.github.io"/>}}
          />
        </p>
      </div>
    </section>
    <footer>
      {/* Do not translate "Impressum", it's needed for German GDPR */}
      <a className="link" onClick={() => {setPopup(PopupType.impressum)}}>Impressum</a>
      <a className="link" onClick={() => {setPopup(PopupType.privacy)}}>{t("Privacy Policy")}</a>
    </footer>
  </div>

  function fetch_stats() {
    fetch(`${window.location.origin}/data/stats`)
      .then(response => {
        if (response.ok) {
          return response.text();
        } else { throw ""; }
      })
      .then(data => {
        // Parse the CSV content
        const lines = data.split('\n');
        const [header, line2] = lines;
        if (!(header.replace(' ', '').startsWith("CPU,MEM"))) {
          console.info("Not displaying server stats: received unexpected: ", header);
        }
        if (line2) {
          let values = line2.split(',');
          setUsageCPU(100 * parseFloat(values[0]));
          setUsageMem(100 * parseFloat(values[1]));
        }
      }).catch(err => {
        console.info('server stats unavailable');
        console.debug(err);
      });
  }
}

export default LandingPage
