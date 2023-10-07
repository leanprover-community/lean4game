import * as React from 'react'
import { GameIdContext } from "../app"
import { InputModeContext, MobileContext, WorldLevelIdContext } from "./infoview/context"
import { GameInfo, useGetGameInfoQuery } from '../state/api'
import { changedOpenedIntro, selectCompleted, selectDifficulty, selectProgress } from '../state/progress'
import { useSelector } from 'react-redux'
import { useAppDispatch, useAppSelector } from '../hooks'
import { Button } from './button'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faDownload, faUpload, faEraser, faBook, faGlobe, faHome, faArrowRight, faArrowLeft, faXmark, faBars, faCode, faCircleInfo, faTerminal } from '@fortawesome/free-solid-svg-icons'
import { PrivacyPolicyPopup } from './privacy_policy'
import { WorldSelectionMenu, downloadFile } from './world_tree'

/** navigation to switch between pages on mobile */
function MobileNav({pageNumber, setPageNumber}:
  { pageNumber: number,
    setPageNumber: any}) {
  const gameId = React.useContext(GameIdContext)
  const dispatch = useAppDispatch()

  let prevText = {0 : null, 1: "Intro", 2: null}[pageNumber]
  let prevIcon = {0 : null, 1: null, 2: faXmark}[pageNumber]
  let prevTitle = {
    0: null,
    1: "Game Introduction",
    2: "World selection"}[pageNumber]
  let nextText = {0 : "Start", 1: null, 2: null}[pageNumber]
  let nextIcon = {0 : null, 1: faBook, 2: null}[pageNumber]
  let nextTitle = {
    0: "World selection",
    1: "Inventory",
    2: null}[pageNumber]

  return <>
    {(prevText || prevTitle || prevIcon) &&
      <Button className="btn btn-inverted toggle-width" to={pageNumber == 0 ? "/" : ""} inverted="true" title={prevTitle}
          onClick={() => {pageNumber == 0 ? null : setPageNumber(pageNumber - 1)}}>
        {prevIcon && <FontAwesomeIcon icon={prevIcon} />}
        {prevText && `${prevText}`}
      </Button>
    }
    {(nextText || nextTitle || nextIcon) &&
      <Button className="btn btn-inverted toggle-width" to="" inverted="true"
          title={nextTitle} onClick={() => {
            console.log(`page number: ${pageNumber}`)
            setPageNumber(pageNumber+1);
            dispatch(changedOpenedIntro({game: gameId, openedIntro: true}))}}>
        {nextText && `${nextText}`}
        {nextIcon && <FontAwesomeIcon icon={nextIcon} />}
      </Button>
    }
  </>
}

export function WelcomeAppBar({gameInfo, toggleImpressum, openEraseMenu, openUploadMenu, toggleInfo} : {
  gameInfo: GameInfo,
  toggleImpressum: any,
  openEraseMenu: any,
  openUploadMenu: any,
  toggleInfo: any
}) {
  const gameId = React.useContext(GameIdContext)
  const {mobile, pageNumber, setPageNumber} = React.useContext(MobileContext)
  const [navOpen, setNavOpen] = React.useState(false)



  /** Download the current progress (i.e. what's saved in the browser store) */
  const gameProgress = useSelector(selectProgress(gameId))
  const downloadProgress = (e) => {
    e.preventDefault()
    downloadFile({
      data: JSON.stringify(gameProgress, null, 2),
      fileName: `lean4game-${gameId}-${new Date().toLocaleDateString()}.json`,
      fileType: 'text/json',
    })
  }


  return   <div className="app-bar" >
    <>
      <div>
        <Button inverted="false" title="back to games selection" to="/">
          <FontAwesomeIcon icon={faArrowLeft} />&nbsp;<FontAwesomeIcon icon={faGlobe} />
        </Button>
        <span className="app-bar-title"></span>
      </div>
      <div>
        <span className="app-bar-title">
          {mobile ? '' : gameInfo?.title}
        </span>
      </div>
      <div className="nav-btns">
        {mobile && <>
          {/* BUTTONS for MOBILE */}
          <MobileNav pageNumber={pageNumber} setPageNumber={setPageNumber} />

        </>}

        <Button to="" className="btn toggle-width" id="menu-btn" onClick={(ev) => {setNavOpen(!navOpen)}} >
          {navOpen ? <FontAwesomeIcon icon={faXmark} /> : <FontAwesomeIcon icon={faBars} />}
        </Button>

      </div>
      <div className={'menu dropdown' + (navOpen ? '' : ' hidden')}>
        {/* {levelId < gameInfo.data?.worldSize[worldId] &&
          <Button inverted="true"
              to={`/${gameId}/world/${worldId}/level/${levelId + 1}`} title="next level"
              disabled={difficulty >= 2 && !(completed || levelId == 0)}
              onClick={() => setNavOpen(false)}>
            <FontAwesomeIcon icon={faArrowRight} />&nbsp;{levelId ? "Next" : "Start"}
          </Button>
        }
        {levelId > 0 && <>
              <Button disabled={levelId <= 0} inverted="true"
                  to={`/${gameId}/world/${worldId}/level/${levelId - 1}`}
                  title="previous level"
                  onClick={() => setNavOpen(false)}>
                <FontAwesomeIcon icon={faArrowLeft} />&nbsp;Previous
              </Button>
            </>}
        <Button to={`/${gameId}`} inverted="true" title="back to world selection">
          <FontAwesomeIcon icon={faHome} />&nbsp;Home
        </Button>
        <Button disabled={levelId <= 0} inverted="true" to=""
            onClick={(ev) => { setTypewriterMode(!typewriterMode); setNavOpen(false) }}
            title="toggle Editor mode">
          <FontAwesomeIcon icon={faCode} />&nbsp;Toggle Editor
        </Button> */}

        <Button title="Game Info & Credits" inverted="true" to="" onClick={(ev) => {toggleInfo(); setNavOpen(false)}}>
          <FontAwesomeIcon icon={faCircleInfo} />&nbsp;Game Info
        </Button>
        <Button title="Clear Progress" inverted="true" to="" onClick={(ev) => {openEraseMenu(); setNavOpen(false)}}>
          <FontAwesomeIcon icon={faEraser} />&nbsp;Erase
        </Button>
        <Button title="Download Progress" inverted="true" to="" onClick={(ev) => {downloadProgress(ev); setNavOpen(false)}}>
          <FontAwesomeIcon icon={faDownload} />&nbsp;Download
        </Button>
        <Button title="Load Progress from JSON" inverted="true" to="" onClick={(ev) => {openUploadMenu(); setNavOpen(false)}}>
          <FontAwesomeIcon icon={faUpload} />&nbsp;Upload
        </Button>
        <Button title="Impressum, privacy policy" inverted="true" to="" onClick={(ev) => {toggleImpressum(); setNavOpen(false)}}>
          <FontAwesomeIcon icon={faCircleInfo} />&nbsp;Impressum
        </Button>
      </div>
    </>
  </div>



}

// /** The menu that is shown next to the world selection graph */
// function WorldSelectionMenu() {
//   const [file, setFile] = React.useState<File>();

//   const gameId = React.useContext(GameIdContext)
//   const store = useStore()
//   const difficulty = useSelector(selectDifficulty(gameId))


//   /* state variables to toggle the pop-up menus */
//   const [eraseMenu, setEraseMenu] = React.useState(false);
//   const openEraseMenu = () => setEraseMenu(true);
//   const closeEraseMenu = () => setEraseMenu(false);
//   const [uploadMenu, setUploadMenu] = React.useState(false);
//   const openUploadMenu = () => setUploadMenu(true);
//   const closeUploadMenu = () => setUploadMenu(false);

//   const gameProgress = useSelector(selectProgress(gameId))
//   const dispatch = useAppDispatch()

//   /** Download the current progress (i.e. what's saved in the browser store) */
//   const downloadProgress = (e) => {
//     e.preventDefault()
//     downloadFile({
//       data: JSON.stringify(gameProgress, null, 2),
//       fileName: `lean4game-${gameId}-${new Date().toLocaleDateString()}.json`,
//       fileType: 'text/json',
//     })
//   }

//   const handleFileChange = (e) => {
//     if (e.target.files) {
//       setFile(e.target.files[0])
//     }
//   }

//   /** Upload progress from a  */
//   const uploadProgress = (e) => {
//     if (!file) {return}
//     const fileReader = new FileReader()
//     fileReader.readAsText(file, "UTF-8")
//     fileReader.onload = (e) => {
//       const data = JSON.parse(e.target.result.toString()) as GameProgressState
//       console.debug("Json Data", data)
//       dispatch(loadProgress({game: gameId, data: data}))
//     }
//     closeUploadMenu()
//   }

//   const eraseProgress = () => {
//     dispatch(deleteProgress({game: gameId}))
//     closeEraseMenu()
//   }

//   const downloadAndErase = (e) => {
//     downloadProgress(e)
//     eraseProgress()
//   }

//   function label(x : number) {
//     return x == 0 ? 'none' : x == 1 ? 'lax' : 'regular'
//   }

//   return <nav className="world-selection-menu">
//     <Button onClick={downloadProgress} title="Download game progress" to=""><FontAwesomeIcon icon={faDownload} /></Button>
//     <Button title="Load game progress from JSON" onClick={openUploadMenu} to=""><FontAwesomeIcon icon={faUpload} /></Button>
//     <Button title="Clear game progress" to="" onClick={openEraseMenu}><FontAwesomeIcon icon={faEraser} /></Button>
//     <div className="slider-wrap">
//       <span className="difficulty-label">Game Rules:</span>
//       <Slider
//         title="Game Rules:&#10;- regular: 🔐 levels, 🔐 tactics&#10;- lax: 🔓 levels, 🔐 tactics&#10;- none: 🔓 levels, 🔓 tactics"
//         min={0} max={2}
//         aria-label="Game Rules"
//         defaultValue={difficulty}
//         marks={[
//           {value: 0, label: label(0)},
//           {value: 1, label: label(1)},
//           {value: 2, label: label(2)}
//         ]}
//         valueLabelFormat={label}
//         getAriaValueText={label}
//         valueLabelDisplay="auto"
//         onChange={(ev, val: number) => {
//           dispatch(changedDifficulty({game: gameId, difficulty: val}))
//         }}
//         ></Slider>

//     </div>
//     {eraseMenu?
//       <div className="modal-wrapper">
//         <div className="modal-backdrop" onClick={closeEraseMenu} />
//         <div className="modal">
//           <div className="codicon codicon-close modal-close" onClick={closeEraseMenu}></div>
//           <h2>Delete Progress?</h2>

//           <p>Do you want to delete your saved progress irreversibly?</p>
//           <p>
//             (This deletes your proofs and your collected inventory.
//             Saves from other games are not deleted.)
//           </p>

//           <Button onClick={eraseProgress} to="">Delete</Button>
//           <Button onClick={downloadAndErase} to="">Download & Delete</Button>
//           <Button onClick={closeEraseMenu} to="">Cancel</Button>
//         </div>
//       </div> : null}
//     {uploadMenu ?
//       <div className="modal-wrapper">
//         <div className="modal-backdrop" onClick={closeUploadMenu} />
//         <div className="modal">
//           <div className="codicon codicon-close modal-close" onClick={closeUploadMenu}></div>
//           <h2>Upload Saved Progress</h2>

//           <p>Select a JSON file with the saved game progress to load your progress.</p>

//           <p><b>Warning:</b> This will delete your current game progress!
//             Consider <a className="download-link" onClick={downloadProgress} >downloading your current progress</a> first!</p>

//           <input type="file" onChange={handleFileChange}/>

//           <Button to="" onClick={uploadProgress}>Load selected file</Button>
//         </div>
//       </div> : null}
//   </nav>
// }


/** The top-navigation bar */
export function LevelAppBar({
    isLoading, levelTitle, impressum, toggleImpressum,
    pageNumber = undefined, setPageNumber = undefined}) {
  const gameId = React.useContext(GameIdContext)
  const {worldId, levelId} = React.useContext(WorldLevelIdContext)
  const gameInfo = useGetGameInfoQuery({game: gameId})

  const {mobile} = React.useContext(MobileContext)

  const difficulty = useSelector(selectDifficulty(gameId))
  const completed = useAppSelector(selectCompleted(gameId, worldId, levelId))

  const { typewriterMode, setTypewriterMode } = React.useContext(InputModeContext)

  const [navOpen, setNavOpen] = React.useState(false)

  return <div className="app-bar" style={isLoading ? {display: "none"} : null} >
    {mobile ?
      <>
        {/* MOBILE VERSION */}
        <div>
          <span className="app-bar-title">
            {levelTitle}
          </span>
        </div>
        <div className="nav-btns">
          {mobile && pageNumber == 0 ?
            <Button to="" className="btn btn-inverted toggle-width"
                title="show inventory" inverted="true" onClick={() => {setPageNumber(1)}}>
              <FontAwesomeIcon icon={faBook}/>
            </Button>
          : pageNumber == 1 &&
            <Button className="btn btn-inverted toggle-width" to=""
                title="show inventory" inverted="true" onClick={() => {setPageNumber(0)}}>
              <FontAwesomeIcon icon={faXmark}/>
            </Button>
          }
          <Button to="" className="btn toggle-width" id="menu-btn" onClick={(ev) => {setNavOpen(!navOpen)}} >
            {navOpen ? <FontAwesomeIcon icon={faXmark} /> : <FontAwesomeIcon icon={faBars} />}
          </Button>
        </div>
        <div className={'menu dropdown' + (navOpen ? '' : ' hidden')}>
          {levelId < gameInfo.data?.worldSize[worldId] &&
            <Button inverted="true"
                to={`/${gameId}/world/${worldId}/level/${levelId + 1}`} title="next level"
                disabled={difficulty >= 2 && !(completed || levelId == 0)}
                onClick={() => setNavOpen(false)}>
              <FontAwesomeIcon icon={faArrowRight} />&nbsp;{levelId ? "Next" : "Start"}
            </Button>
          }
          {levelId > 0 && <>
                <Button disabled={levelId <= 0} inverted="true"
                    to={`/${gameId}/world/${worldId}/level/${levelId - 1}`}
                    title="previous level"
                    onClick={() => setNavOpen(false)}>
                  <FontAwesomeIcon icon={faArrowLeft} />&nbsp;Previous
                </Button>
              </>}
          <Button to={`/${gameId}`} inverted="true" title="back to world selection">
            <FontAwesomeIcon icon={faHome} />&nbsp;Home
          </Button>
          <Button disabled={levelId <= 0} inverted="true" to=""
              onClick={(ev) => { setTypewriterMode(!typewriterMode); setNavOpen(false) }}
              title={typewriterMode ? "Editor mode" : "Typewriter mode"}>
            <FontAwesomeIcon icon={typewriterMode ? faCode : faTerminal} />
            &nbsp;{typewriterMode ? "Editor mode" : "Typewriter mode"}
          </Button>
          <Button title="information, Impressum, privacy policy" inverted="true" to="" onClick={(ev) => {toggleImpressum(ev); setNavOpen(false)}}>
            <FontAwesomeIcon icon={faCircleInfo} />&nbsp;Info &amp; Impressum
          </Button>
        </div>
      </>
    :
      <>
        {/* DESKTOP VERSION */}
        <div>
          <Button to={`/${gameId}`} inverted="true" title="back to world selection" id="home-btn">
            <FontAwesomeIcon icon={faHome} />
          </Button>
          <span className="app-bar-title">
            {gameInfo.data?.worlds.nodes[worldId].title && `World: ${gameInfo.data?.worlds.nodes[worldId].title}`}
          </span>
        </div>
        <div>
          <span className="app-bar-title">
            {levelTitle}
          </span>
        </div>
        <div className="nav-btns">
          {levelId > 0 && <>
            <Button disabled={levelId <= 0} inverted="true"
                to={`/${gameId}/world/${worldId}/level/${levelId - 1}`}
                title="previous level"
                onClick={() => setNavOpen(false)}>
              <FontAwesomeIcon icon={faArrowLeft} />&nbsp;Previous
            </Button>
          </>}
          {levelId < gameInfo.data?.worldSize[worldId] ?
            <Button inverted="true"
                to={`/${gameId}/world/${worldId}/level/${levelId + 1}`} title="next level"
                disabled={difficulty >= 2 && !(completed || levelId == 0)}
                onClick={() => setNavOpen(false)}>
              <FontAwesomeIcon icon={faArrowRight} />&nbsp;{levelId ? "Next" : "Start"}
            </Button>
            :
            <Button to={`/${gameId}`} inverted="true" title="back to world selection" id="home-btn">
              <FontAwesomeIcon icon={faHome} />&nbsp;Leave World
            </Button>
          }
          <Button className="btn btn-inverted toggle-width" disabled={levelId <= 0} inverted="true" to=""
              onClick={(ev) => { setTypewriterMode(!typewriterMode); setNavOpen(false) }}
              title={typewriterMode ? "Editor mode" : "Typewriter mode"}>
            <FontAwesomeIcon icon={typewriterMode ? faCode : faTerminal} />
          </Button>
          <Button className="btn btn-inverted toggle-width" title="information, Impressum, privacy policy" inverted="true" to="" onClick={(ev) => {toggleImpressum(ev); setNavOpen(false)}}>
            <FontAwesomeIcon icon={impressum ? faXmark : faCircleInfo} />
          </Button>
        </div>
      </>
    }
  </div>
}
