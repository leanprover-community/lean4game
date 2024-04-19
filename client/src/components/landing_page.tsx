import * as React from 'react';
import { useNavigate } from "react-router-dom";
import { Trans, useTranslation } from 'react-i18next';

import '@fontsource/roboto/300.css';
import '@fontsource/roboto/400.css';
import '@fontsource/roboto/500.css';
import '@fontsource/roboto/700.css';

import '../css/landing_page.css'
import bgImage from '../assets/bg.jpg'

import { useGetGameInfoQuery } from '../state/api'

import { ImpressumButton, MenuButton, PreferencesButton, PrivacyButton } from './app_bar';
import lean4gameConfig from '../config.json'
import i18next from 'i18next';
import { popupAtom, PopupType } from '../store/popup-atoms';
import { useAtom } from 'jotai';
import { GithubIcon } from './navigation/github_icon';
import { Tile } from './landing_page/tile';
import { navOpenAtom } from '../store/navigation-atoms';


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
            { usageMem >= 0 && <> {t("RAM")}: <strong>{usageMem.toFixed(2)} %</strong>{t(" used")}.<br/></> }
            { usageCPU >= 0 && <> {t("CPU")}: <strong>{usageCPU.toFixed(2)} %</strong>{t(" used")}. </> }
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
