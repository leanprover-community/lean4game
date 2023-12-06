import * as React from 'react';
import { useNavigate, Link } from "react-router-dom";

import '@fontsource/roboto/300.css';
import '@fontsource/roboto/400.css';
import '@fontsource/roboto/500.css';
import '@fontsource/roboto/700.css';

import '../css/landing_page.css'
import coverRobo from '../assets/covers/formaloversum.png'
import coverNNG from '../assets/covers/nng.png'
import bgImage from '../assets/bg.jpg'

import Markdown from './markdown';
import {PrivacyPolicyPopup} from './popup/privacy_policy'
import { GameTile, useGetGameInfoQuery } from '../state/api'

const flag = {
  'Dutch': '🇳🇱',
  'English': '🇬🇧',
  'French': '🇫🇷',
  'German': '🇩🇪',
  'Italian': '🇮🇹',
}

function GithubIcon({url='https://github.com'}) {

  return <div className="github-link">
    <a title="view the Lean game server on Github" href={url}>
    <svg height="24" aria-hidden="true" viewBox="0 0 16 16" version="1.1" width="24" className="">
      <path fill="#fff" d="M8 0c4.42 0 8 3.58 8 8a8.013 8.013 0 0 1-5.45 7.59c-.4.08-.55-.17-.55-.38 0-.27.01-1.13.01-2.2 0-.75-.25-1.23-.54-1.48 1.78-.2 3.65-.88 3.65-3.95 0-.88-.31-1.59-.82-2.15.08-.2.36-1.02-.08-2.12 0 0-.67-.22-2.2.82-.64-.18-1.32-.27-2-.27-.68 0-1.36.09-2 .27-1.53-1.03-2.2-.82-2.2-.82-.44 1.1-.16 1.92-.08 2.12-.51.56-.82 1.28-.82 2.15 0 3.06 1.86 3.75 3.64 3.95-.23.2-.44.55-.51 1.07-.46.21-1.61.55-2.33-.66-.15-.24-.6-.83-1.23-.82-.67.01-.27.38.01.53.34.19.73.9.82 1.13.16.45.68 1.31 2.69.94 0 .67.01 1.3.01 1.49 0 .21-.15.45-.55.38A7.995 7.995 0 0 1 0 8c0-4.42 3.58-8 8-8Z"></path>
    </svg>
    </a>
    </div>
}

function Tile({gameId, data}: {gameId: string, data: GameTile|undefined}) {

  let navigate = useNavigate();
  const routeChange = () =>{
    navigate(gameId);
  }

  if (typeof data === 'undefined') {
    return <></>
  }

  return <div className="game" onClick={routeChange}>
    <div className="wrapper">
      <div className="title">{data.title}</div>
      <div className="short-description">{data.short}
      </div>
      { data.image ? <img className="image" src={data.image} alt="" /> : <div className="image"/> }
      <div className="long description"><Markdown>{data.long}</Markdown></div>
    </div>
    <table className="info">
      <tbody>
      <tr>
        <td title="consider playing these games first.">Prerequisites</td>
        <td><Markdown>{data.prerequisites.join(', ')}</Markdown></td>
      </tr>
      <tr>
        <td>Worlds</td>
        <td>{data.worlds}</td>
      </tr>
      <tr>
        <td>Levels</td>
        <td>{data.levels}</td>
      </tr>
      <tr>
        <td>Language</td>
        <td title={`in ${data.languages.join(', ')}`}>{data.languages.map((lan) => flag[lan]).join(', ')}</td>
      </tr>
      </tbody>
    </table>
  </div>

}

function LandingPage() {

  const navigate = useNavigate();

  const [impressum, setImpressum] = React.useState(false);
  const openImpressum = () => setImpressum(true);
  const closeImpressum = () => setImpressum(false);

  // const [allGames, setAllGames] = React.useState([])
  // const [allTiles, setAllTiles] = React.useState([])

  // const getTiles=()=>{
  //   fetch('featured_games.json', {
  //     headers : {
  //       'Content-Type': 'application/json',
  //       'Accept': 'application/json'
  //     }
  //   }
  //   ).then(function(response){
  //     return response.json()
  //   }).then(function(data) {
  //     setAllGames(data.featured_games)

  //   })
  // }

  // React.useEffect(()=>{
  //   getTiles()
  // },[])

  // React.useEffect(()=>{

  //   Promise.allSettled(
  //     allGames.map((gameId) => (
  //       fetch(`data/g/${gameId}/game.json`).catch(err => {return undefined})))
  //   ).then(responses =>
  //     responses.forEach((result) => console.log(result)))
  //   //   Promise.all(responses.map(res => {
  //   //     if (res.status == "fulfilled") {
  //   //       console.log(res.value.json())
  //   //       return res.value.json()
  //   //     } else {
  //   //       return undefined
  //   //     }
  //   //   }))
  //   // ).then(allData => {
  //   //   setAllTiles(allData.map(data => data?.tile))
  //   // })
  // },[allGames])

  // TODO: I would like to read the supported games list form a JSON,
  // Then load all these games in
  //
  let allGames = [
    "leanprover-community/nng4",
    "djvelleman/stg4",
    "hhu-adam/robo"]
  let allTiles = allGames.map((gameId) => (useGetGameInfoQuery({game: `g/${gameId}`}).data?.tile))

  return <div className="landing-page">
    <header style={{backgroundImage: `url(${bgImage})`}}>
      <nav>
        <GithubIcon url="https://github.com/leanprover-community/lean4game"/>
      </nav>
      <div id="main-title">
        <h1>Lean Game Server</h1>
        <p>
          A repository of learning games for the
          proof assistant <a target="_blank" href="https://leanprover-community.github.io/">Lean</a> <i>(Lean 4)</i> and
          its mathematical library <a target="_blank" href="https://github.com/leanprover-community/mathlib4">mathlib</a>
        </p>
      </div>
    </header>
    <div className="game-list">
      {allTiles.length == 0 ?
        <p>No Games loaded. Use <a>http://localhost:3000/#/g/local/FOLDER</a> to open a
          game directly from a local folder.
        </p>
        : allGames.map((id, i) => (
          <Tile
            key={id}
            gameId={`g/${id}`}
            data={allTiles[i]}
          />
        ))
      }
      {/* <GameTile
        title="Natural Number Game"
        gameId="g/hhu-adam/NNG4"
        intro="The classical introduction game for Lean."
        description="In this game you recreate the natural numbers $\mathbb{N}$ from the Peano axioms,
learning the basics about theorem proving in Lean.

This is a good first introduction to Lean!"
        worlds="8"
        levels="67"
        image={coverNNG}
        language="English"
        />

      <GameTile
        title="Set Theory Game"
        gameId="g/djvelleman/STG4"
        intro="A game about set theory"
        description=""
        worlds="5"
        levels="30"
        language="English"
        />
   */}
    </div>
    <section>
      <div className="wrapper">
        <h2>Development notes</h2>
        <p>
          As this server runs lean on our university machines, it has a limited capacity.
          Our current estimate is about 55 copies of the NNG or 25 copies of games importing
          mathlib. We hope to address this limitation in the future.
        </p>
        <p>
          Most aspects of the games and the infrastructure are still in development. Feel free to
          file a <a target="_blank" href="https://github.com/leanprover-community/lean4game/issues">GitHub Issue</a> about
          any problems you experience!
        </p>
      </div>
    </section>
    <section>
      <div className="wrapper">
        <h2>Adding new games</h2>
        <p>
          If you are considering writing your own game, you should use
          the <a target="_blank" href="https://github.com/hhu-adam/NNG4">NNG Github Repo</a> as
          a template.
        </p>
        <p>
          There is an option to load and run your own games directly on the server,
          instructions are in the NNG repo. Since this is still in development we'd like to
          encourage you to contact us for support creating your own game. The documentation is
          not polished yet.
        </p>
        <p>
          To add games to this main page, you should get in contact as
          games will need to be added manually.
        </p>
      </div>
    </section>
    <section>
      <div className="wrapper">
        <h2>Funding</h2>
        <p>
          This server has been developed as part of the
          project <a target="_blank" href="https://hhu-adam.github.io">ADAM : Anticipating the Digital Age of Mathematics</a> at
          Heinrich-Heine-Universität in Düsseldorf.
        </p>
      </div>
    </section>
    <footer>
      <a className="link" onClick={openImpressum}>Impressum</a>
      {impressum? <PrivacyPolicyPopup handleClose={closeImpressum} />: null}
    </footer>

    {/* <PrivacyPolicy/> */}

  </div>

}

export default LandingPage
