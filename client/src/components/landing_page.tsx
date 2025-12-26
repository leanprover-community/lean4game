import * as React from 'react';
import { useEffect } from 'react';

import { useNavigate } from "react-router-dom";
import { I18nextProvider, Trans, useTranslation } from 'react-i18next';

import '@fontsource/roboto/300.css';
import '@fontsource/roboto/400.css';
import '@fontsource/roboto/500.css';
import '@fontsource/roboto/700.css';

import '../css/landing_page.css'
import bgImage from '../assets/bg.jpg'

import { Markdown } from './markdown';
import { GameTile, useGetGameInfoQuery } from '../state/api'
import path from 'path';

import { ImpressumButton, MenuButton, PreferencesButton, PrivacyButton } from './app_bar';
import ReactCountryFlag from 'react-country-flag';
import lean4gameConfig from '../config.json'
import i18next from 'i18next';
import i18n from 'i18next';
import { popupAtom, PopupType } from '../store/popup-atoms';
import { useAtom } from 'jotai';
import { GithubIcon } from './navigation/github_icon';
import { useGameTranslation } from '../utils/translation';
import { navOpenAtom } from '../store/navigation-atoms';

function ScopedI18n({ lng, children }: { lng: string, children: React.ReactNode}) {
  const scopedI18n = i18n.createInstance()

  scopedI18n.init({
    lng,
    fallbackLng: 'en',
    resources: { en: {}, de: {} },
  });

  return <I18nextProvider i18n={scopedI18n}>{children}</I18nextProvider>;
}

function Tile({gameId, data}: {gameId: string, data: GameTile|undefined}) {
  let { t, i18n } = useTranslation()

  let navigate = useNavigate();

  const routeChange = () =>{
    navigate(gameId);
  }

  if (typeof data === 'undefined') {
    return <></>
  }

  return <div className="game" onClick={routeChange}>
      <div className="wrapper">
        <div className="title">{t(data.title, {ns: gameId})}</div>
        <div className="short-description">{t(data.short, { ns: gameId })}
        </div>
        { data.image ? <img className="image" src={path.join("data", gameId, data.image)} alt="" /> : <div className="image"/> }
        <div className="long description"><Markdown>{t(data.long, { ns: gameId })}</Markdown></div>
      </div>
      <table className="info">
        <tbody>
        <tr>
          <td title="consider playing these games first.">{t("Prerequisites")}</td>
          <td><Markdown>{t(data.prerequisites.join(', '), { ns: gameId })}</Markdown></td>
        </tr>
        <tr>
          <td>{t("Worlds")}</td>
          <td>{data.worlds}</td>
        </tr>
        <tr>
          <td>{t("Levels")}</td>
          <td>{data.levels}</td>
        </tr>
        <tr className="languages">
          <td>{t("Language")}</td>

          <td>
            {data.languages.map((lang) => {
              let langOpt = lean4gameConfig.languages.find((e) => e.iso == lang)
              if (lean4gameConfig.useFlags) {
                return <ReactCountryFlag key={`flag-${lang}`} title={langOpt?.name} countryCode={langOpt?.flag} className="emojiFlag"/>
              } else {
                return <span title={langOpt?.name}>{lang}</span>
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
  const [navOpen, setNavOpen] = useAtom(navOpenAtom)

  const [usageCPU, setUsageCPU] = React.useState<number>()
  const [usageMem, setUsageMem] = React.useState<number>()

  const { t, i18n } = useTranslation()

  // Load the namespaces of all games
  // TODO: should `allGames` contain game-ids starting with `g/`?
  i18next.loadNamespaces(lean4gameConfig.allGames.map(id => `g/${id}`))

  let allTiles = lean4gameConfig.allGames.map((gameId) => {
    let q =  useGetGameInfoQuery({game: `g/${gameId}`})

    // if (q.isError) {
    //   if (q.error?.originalStatus === 404) {
    //     // Handle 404 error
    //     console.log('File not found');
    //   } else {
    //     // Suppress additional console.error messages
    //     console.error(q.error);
    //   }
    // }

    return q.data?.tile
  })

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
        <GithubIcon url="https://github.com/leanprover-community/lean4game"/>
        <MenuButton />
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
      {allTiles.filter(x => x != null).length == 0 ?
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
            data={allTiles[i]}
          />
        ))
      }
    </div>
    { // show server capacity from `games/stats.csv` if present
      (usageMem >= 0 || usageCPU >= 0 ) &&
      <section>
        <div className="wrapper">
          <h2>{t("Server capacity.translation", { defaultValue: "Server capacity" })}</h2>
          <Trans
            i18nKey="Server capacity.description"
            defaults="<p>As this server runs lean on our university machines, it has a limited capacity. Our current estimate is about 70 simultaneous games.</p>"
          />
          <p>
            { usageMem >= 0 && <> {t("RAM")}: <strong>{usageMem.toFixed(2)} %</strong>{t(" used")}.<br/></> }
            { usageCPU >= 0 && <> {t("CPU")}: <strong>{usageCPU.toFixed(2)} %</strong>{t(" used")}. </> }
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
