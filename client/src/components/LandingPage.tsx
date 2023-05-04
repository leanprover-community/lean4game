import * as React from 'react';
import { useNavigate } from "react-router-dom";
import { Link } from 'react-router-dom';
import Markdown from './Markdown';

import '@fontsource/roboto/300.css';
import '@fontsource/roboto/400.css';
import '@fontsource/roboto/500.css';
import '@fontsource/roboto/700.css';

import './LandingPage.css'
import {PrivacyPolicyPopup} from './PrivacyPolicy'

import coverRobo from '../assets/covers/formaloversum.png'
import bgImage from '../assets/bg.jpg'

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
    <svg height="24
    " aria-hidden="true" viewBox="0 0 16 16" version="1.1" width="24" className="">
      <circle className="world-circle" cx="8" cy="8" r="8" fill="#fff"/>
        <path d="M8 0c4.42 0 8 3.58 8 8a8.013 8.013 0 0 1-5.45 7.59c-.4.08-.55-.17-.55-.38 0-.27.01-1.13.01-2.2 0-.75-.25-1.23-.54-1.48 1.78-.2 3.65-.88 3.65-3.95 0-.88-.31-1.59-.82-2.15.08-.2.36-1.02-.08-2.12 0 0-.67-.22-2.2.82-.64-.18-1.32-.27-2-.27-.68 0-1.36.09-2 .27-1.53-1.03-2.2-.82-2.2-.82-.44 1.1-.16 1.92-.08 2.12-.51.56-.82 1.28-.82 2.15 0 3.06 1.86 3.75 3.64 3.95-.23.2-.44.55-.51 1.07-.46.21-1.61.55-2.33-.66-.15-.24-.6-.83-1.23-.82-.67.01-.27.38.01.53.34.19.73.9.82 1.13.16.45.68 1.31 2.69.94 0 .67.01 1.3.01 1.49 0 .21-.15.45-.55.38A7.995 7.995 0 0 1 0 8c0-4.42 3.58-8 8-8Z"></path>
    </svg>
    </a>
    </div>
}

function GameTile({
  title,
  gameId,
  intro, // Catchy intro phrase.
  image=null,
  worlds='?',
  levels='?',
  prereq='&ndash;', // Optional list of games that this game builds on. Use markdown.
  description, // Longer description. Supports Markdown.
  language}) {

  let navigate = useNavigate();
  const routeChange = () =>{
    let path = `game/${gameId}`;
    navigate(path);
  }

  return <div className="game" onClick={routeChange}>
    <div className="wrapper">
      <div className="title">{title}</div>
      <div className="short-description">{intro}
      </div>
      { image ? <img className="image" src={image} alt="" /> : <div className="image"/> }
      <div className="long description"><Markdown>{description}</Markdown></div>
    </div>
    <table className="info">
      <tr>
        <td title="consider playing these games first.">Prerequisites</td>
        <td><Markdown>{prereq}</Markdown></td>
      </tr>
      <tr>
        <td>Worlds</td>
        <td>{worlds}</td>
      </tr>
      <tr>
        <td>Levels</td>
        <td>{levels}</td>
      </tr>
      <tr>
        <td>Language</td>
        <td title={`in ${language}`}>{flag[language]}</td>
      </tr>
    </table>
  </div>

}

function LandingPage() {

  const navigate = useNavigate();

  const [impressum, setImpressum] = React.useState(false);
  const openImpressum = () => setImpressum(true);
  const closeImpressum = () => setImpressum(false);


  return <div className="landing-page">
    <header style={{backgroundImage: `url(${bgImage})`}}>
      <nav>
        <GithubIcon url="https://github.com/leanprover-community/lean4game"/>
      </nav>
      <div id="main-title">
        <h1>Lean Game Server</h1>
        <p>
          This server hosts learning games for the
          proof assistant <a target="_blank" href="https://leanprover-community.github.io/">Lean</a> <i>(lean4)</i> and
          its mathematical library <a target="_blank" href="https://github.com/leanprover-community/mathlib4">Mathlib</a>.
        </p>
      </div>
    </header>

    <div className="game-list">

      <GameTile
        title="Formaloversum"
        gameId="adam"
        intro="Erkunde das Leansche Universum mit deinem Robo, welcher dir bei der Verständigung mit den Formalosophen zur Seite steht."
        description="
Dieses Spiel führt die Grundlagen zur Beweisführung in Lean ein und schneidet danach verschiedene Bereiche des Bachelorstudiums an.

(Das Spiel befindet sich noch in der Entstehungsphase.)
"
        image={coverRobo}
        language="German"
        />

      <GameTile
        title="Natural Number Game"
        gameId="nng"
        intro="The classical introduction game for Lean."
        description="In this game you recreate the natural numbers $\mathbb{N}$ from the Peano axioms,
learning the basics about theorem proving in Lean.

This is a good first introduction to Lean!"
        worlds="9"
        levels="72"
        language="English"
        />
    </div>
    <section>
      <h2>Development notes</h2>
      <p>
        As this server runs lean on our university machines, it has a capacity of ca. 15-25
        games running simultaneously. We hope to address this limitation in the further future.
      </p>
      <p>
        Most things about the games and infrastructure is still in development. Feel free to
        write <a target="_blank" href="https://github.com/leanprover-community/lean4game/issues">Github Issues</a> about
        any problems you experience!
      </p>
    </section>
    <section>
      <h2>Adding new games</h2>
      <p>
        If you consider writing your own game, you should use
        the <a target="_blank" href="https://github.com/hhu-adam/NNG4">NNG Github Repo</a> as
        a template.
      </p>
      <p>
        There will be an option to load and run games through the server
        directly by specifying a URL, but this is still in development.
      </p>
      <p>
        To add games to this page, you should get in contact as
        games will need to be added manually.
      </p>
    </section>
    <section>
      <h2>Funding</h2>
      <p>
        This Server has been developed as part of the
        project <a target="_blank" href="https://hhu-adam.github.io">ADAM : Anticipating the Digital Age of Mathematics</a> at
        Heinrich-Heine-Universität in Düsseldorf.
      </p>
    </section>
    <footer>
      <a className="link" onClick={openImpressum}>Impressum</a>
        {impressum? <PrivacyPolicyPopup handleClose={closeImpressum} />: null}
    </footer>

    {/* <PrivacyPolicy/> */}

  </div>

}

export default LandingPage
