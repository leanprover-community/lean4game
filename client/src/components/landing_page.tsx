import * as React from 'react';
import { useNavigate, Link } from "react-router-dom";
import { Trans, useTranslation } from 'react-i18next';

import '@fontsource/roboto/300.css';
import '@fontsource/roboto/400.css';
import '@fontsource/roboto/500.css';
import '@fontsource/roboto/700.css';

import '../css/landing_page.css'
import bgImage from '../assets/bg.jpg'

import { GameTile } from '../state/api'
import path from 'path';

// import ReactCountryFlag from 'react-country-flag';
import lean4gameConfig from '../config.json'
import i18next from 'i18next';
import { useContext } from 'react';
import { PopupContext } from './popup/popup';
import { Flag } from './flag';
import { Markdown } from './utils';

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
            <Flag key={lang} iso={lang} showTitle={true} />
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

  const [usageCPU, setUsageCPU] = React.useState<number>()
  const [usageMem, setUsageMem] = React.useState<number>()
  const [gameTiles, setGameTiles] = React.useState<Array<JSX.Element>>([])

  const { t } = useTranslation()

  // Load the namespaces of all games
  // TODO: should `allGames` contain game-ids starting with `g/`?
  i18next.loadNamespaces(lean4gameConfig.allGames.map(id => `g/${id}`))

  const devMode = process.env.NODE_ENV == "development"

  /**
   *
   */
  React.useEffect(() => {
    let games = [...lean4gameConfig.allGames]
    const fetchGameInfos = async () => {
      try {
        if (devMode) {
          await fetch(`${window.location.origin}/data/local_games`)
          .then(response => {if (response.ok) {return response.json()} else {throw ""}})
          .then((localGames: string[]) => {
            games = games.concat(localGames.map((game: string) => (`local/${game}`)))
            games.push("test/Test")
          })
        }
        const promises = games.map(async game => {
          try {
            const response = await fetch(`${window.location.origin}/data/g/${game}/Game.json`)
            if (!response.ok) {return null}
            let gameInfo = await response.json()
            return [game, gameInfo.tile]
          } catch (err) {
            console.info(`game ${game} unavailable`)
            console.debug(err)
            return null
          }
        })
        let response = await Promise.all(promises)
        response = response.filter(tile => tile !== null)
        let tiles = response.map(([id, tile]) => {
          return <Tile
            key={id}
            gameId={`g/${id}`}
            data={tile}
          />})
        setGameTiles(tiles)
      } catch (error) {
        console.error("Error fetching data:", error)
      }
    }
    fetchGameInfos()
  }, [])

  /** Parse `games/stats.csv` if present and display server capacity. */
  React.useEffect(() => {
    fetch(`${window.location.origin}/data/stats`)
    .then(response => {if (response.ok) {
      return response.text() } else {throw ""}})
    .then(data => {
      // Parse the CSV content
      const lines = data.split('\n');
      const [header, line2] = lines;
      if (!(header.replace(' ', '').startsWith("CPU,MEM"))) {
        console.info("Not displaying server stats: received unexpected: ", header)
      }
      if (line2) {
        let values = line2.split(',')
        setUsageCPU(100 * parseInt(values[0]));
        setUsageMem(100 * parseInt(values[1]));
      }
    }).catch(err => {
      console.info('server stats unavailable')
      console.debug(err)
    })
  }, [])

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
        { gameTiles }
      </div>
    </React.Suspense>
    { // show server capacity from `games/stats.csv` if present
      (usageMem >= 0 || usageCPU >= 0 ) &&
      <section>
        <div className="wrapper">
          <h2>{t("Server capacity")}</h2>
          <Trans>
            <p>
              As this server runs lean on our university machines, it has a limited capacity.
              Our current estimate is about 70 simultaneous games.
            </p>
          </Trans>
          <p>
            { usageMem >= 0 && <> {t("RAM")}: <strong>{usageMem} %</strong>{t(" used")}.<br/></> }
            { usageCPU >= 0 && <> {t("CPU")}: <strong>{usageCPU} %</strong>{t(" used")}. </> }
          </p>
        </div>
      </section>
    }
    <section>
      <div className="wrapper">
        <h2>{t("Development notes")}</h2>
        <Trans>
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
            project <a target="_blank" href="https://hhu-adam.github.io">ADAM: Anticipating the Digital Age of Mathematics</a> at
            Heinrich Heine University Düsseldorf.
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
