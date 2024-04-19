import * as React from 'react';
import { useNavigate, Link } from "react-router-dom";
import { Trans, useTranslation } from 'react-i18next';

import '@fontsource/roboto/300.css';
import '@fontsource/roboto/400.css';
import '@fontsource/roboto/500.css';
import '@fontsource/roboto/700.css';

import '../css/landing_page.css'
import bgImage from '../assets/bg.jpg'

import Markdown from './markdown';
import {PrivacyPolicyPopup} from './popup/privacy_policy'
import { GameTile, useGetGameInfoQuery } from '../state/api'
import path from 'path';

import { PreferencesPopup } from './popup/preferences';
import { ImpressumButton, MenuButton, PreferencesButton } from './app_bar';
import ReactCountryFlag from 'react-country-flag';
import lean4gameConfig from '../config.json'
import i18next from 'i18next';

function GithubIcon({url='https://github.com'}) {
  let { t } = useTranslation()

  return <div className="github-link">
    <a title={t("view the Lean game server on Github")} href={url}>
    <svg height="24" aria-hidden="true" viewBox="0 0 16 16" version="1.1" width="24" className="">
      <path fill="#fff" d="M8 0c4.42 0 8 3.58 8 8a8.013 8.013 0 0 1-5.45 7.59c-.4.08-.55-.17-.55-.38 0-.27.01-1.13.01-2.2 0-.75-.25-1.23-.54-1.48 1.78-.2 3.65-.88 3.65-3.95 0-.88-.31-1.59-.82-2.15.08-.2.36-1.02-.08-2.12 0 0-.67-.22-2.2.82-.64-.18-1.32-.27-2-.27-.68 0-1.36.09-2 .27-1.53-1.03-2.2-.82-2.2-.82-.44 1.1-.16 1.92-.08 2.12-.51.56-.82 1.28-.82 2.15 0 3.06 1.86 3.75 3.64 3.95-.23.2-.44.55-.51 1.07-.46.21-1.61.55-2.33-.66-.15-.24-.6-.83-1.23-.82-.67.01-.27.38.01.53.34.19.73.9.82 1.13.16.45.68 1.31 2.69.94 0 .67.01 1.3.01 1.49 0 .21-.15.45-.55.38A7.995 7.995 0 0 1 0 8c0-4.42 3.58-8 8-8Z"></path>
    </svg>
    </a>
    </div>
}

function Tile({gameId, data}: {gameId: string, data: GameTile|undefined}) {
  let { t } = useTranslation()
  let navigate = useNavigate();
  const routeChange = () =>{
    navigate(gameId);
  }

  if (typeof data === 'undefined') {
    return <></>
  }

  return <div className="game" onClick={routeChange}>
    <div className="wrapper">
      <div className="title">{t(data.title, { ns: gameId })}</div>
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

  const navigate = useNavigate();

  const [impressumPopup, setImpressumPopup] = React.useState(false);
  const [preferencesPopup, setPreferencesPopup] = React.useState(false);
  const [navOpen, setNavOpen] = React.useState(false);
  const openImpressum = () => setImpressumPopup(true);
  const closeImpressum = () => setImpressumPopup(false);
  const toggleImpressum = () => setImpressumPopup(!impressumPopup);
  const closePreferencesPopup = () => setPreferencesPopup(false);
  const togglePreferencesPopup = () => setPreferencesPopup(!preferencesPopup);

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

  return <div className="landing-page">
    <header style={{backgroundImage: `url(${bgImage})`}}>
      <nav className="landing-page-nav">
        <GithubIcon url="https://github.com/leanprover-community/lean4game"/>
        <MenuButton navOpen={navOpen} setNavOpen={setNavOpen}/>
        <div className={'menu dropdown' + (navOpen ? '' : ' hidden')}>
            <ImpressumButton setNavOpen={setNavOpen} toggleImpressum={toggleImpressum} isDropdown={true} />
            <PreferencesButton setNavOpen={setNavOpen} togglePreferencesPopup={togglePreferencesPopup}/>
        </div>
      </nav>
      <div id="main-title">
        <h1>{t("Lean Game Server")}</h1>
        <p>
          <Trans>
            A repository of learning games for the
            proof assistant <a target="_blank" href="https://leanprover-community.github.io/">Lean</a> <i>(Lean 4)</i> and
            its mathematical library <a target="_blank" href="https://github.com/leanprover-community/mathlib4">mathlib</a>
          </Trans>
        </p>
      </div>
    </header>
    <div className="game-list">
      {allTiles.filter(x => x != null).length == 0 ?
        <p>
          <Trans>
            No Games loaded. Use <a>http://localhost:3000/#/g/local/FOLDER</a> to open a
            game directly from a local folder.
          </Trans>
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
    <section>
      <div className="wrapper">
        <h2>{t("Development notes")}</h2>
        <Trans>
          <p>
            As this server runs lean on our university machines, it has a limited capacity.
            Our current estimate is about 70 simultaneous games.
            We hope to address and test this limitation better in the future.
          </p>
          <p>
            Most aspects of the games and the infrastructure are still in development. Feel free to
            file a <a target="_blank" href="https://github.com/leanprover-community/lean4game/issues">GitHub Issue</a> about
            any problems you experience!
          </p>
        </Trans>
      </div>
    </section>
    <section>
      <div className="wrapper">
        <h2>{t("Adding new games")}</h2>
        <Trans>
          <p>
            If you are considering writing your own game, you should use
            the <a target="_blank" href="https://github.com/hhu-adam/GameSkeleton">GameSkeleton Github Repo</a> as
            a template and read <a target="_blank" href="https://github.com/leanprover-community/lean4game/">How to Create a Game</a>.
          </p>
          <p>
            You can directly load your games into the server and play it using
            the correct URL. The <a target="_blank" href="https://github.com/leanprover-community/lean4game/">instructions above</a> also
            explain the details for how to load your game to the server.

            We'd like to encourage you to contact us if you have any questions.
          </p>
          <p>
            Featured games on this page are added manually.
            Please get in contact and we'll happily add yours.
          </p>
        </Trans>
      </div>
    </section>
    <section>
      <div className="wrapper">
        <h2>{t("Funding")}</h2>
        <p>
          <Trans>
            This server has been developed as part of the
            project <a target="_blank" href="https://hhu-adam.github.io">ADAM : Anticipating the Digital Age of Mathematics</a> at
            Heinrich-Heine-Universität in Düsseldorf.
          </Trans>
        </p>
      </div>
    </section>
    <footer>
      {/* Do not translate "Impressum", it's needed for German GDPR */}
      <a className="link" onClick={openImpressum}>Impressum</a>
      {impressumPopup? <PrivacyPolicyPopup handleClose={closeImpressum} />: null}
      {preferencesPopup ? <PreferencesPopup handleClose={closePreferencesPopup} /> : null}
    </footer>
  </div>

}

export default LandingPage
