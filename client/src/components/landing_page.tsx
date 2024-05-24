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
import { GameTile, useGetGameInfoQuery } from '../state/api'
import path from 'path';

import ReactCountryFlag from 'react-country-flag';
import lean4gameConfig from '../config.json'
import i18next from 'i18next';
import { useContext } from 'react';
import { PopupContext } from './popup/popup';
import { Flag } from './flag';

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
          {data.languages.map((lang) => (
            <Flag iso={lang} showTitle={true} />
          ))}
        </td>
      </tr>
      </tbody>
    </table>
  </div>

}

function LandingPage() {

  const navigate = useNavigate();
  const { setPopupContent } = useContext(PopupContext)

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
    <React.Suspense>
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
    </React.Suspense>
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
      <a className="link" onClick={() => {setPopupContent("impressum")}}>{t("Impressum")}</a>
      <a className="link" onClick={() => {setPopupContent("privacy")}}>{t("Privacy Policy")}</a>
    </footer>
  </div>

}

export default LandingPage
