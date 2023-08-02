/**
 * @fileOverview Define the menu displayed with the tree of worlds on the welcome page
*/
import * as React from 'react'
import { Link } from 'react-router-dom';
import { useStore, useSelector } from 'react-redux';
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faDownload, faUpload, faEraser, faGlobe, faArrowLeft } from '@fortawesome/free-solid-svg-icons'
import { store } from '../state/store';

import './world_selection_menu.css'

import { Button } from './button'
import { GameIdContext } from '../app';
import { useAppDispatch } from '../hooks';
import { deleteProgress, selectProgress, loadProgress, GameProgressState, selectDifficulty, changedDifficulty, selectCompleted } from '../state/progress';
import { Slider } from '@mui/material';
import cytoscape, { LayoutOptions } from 'cytoscape'
import klay from 'cytoscape-klay';

// Settings for the world tree
cytoscape.use( klay )
const N = 18              // max number of levels per world
const R = 64              // radius of a world
const r = 12              // radius of a level
const s = 10              // global scale
const padding = R + 2*r   // padding of the graphic (on a different scale)
const ds = .75            // scale the resulting svg image

// colours
const grey = '#999'
const lightgrey = '#bbb'
const green = 'green'
const lightgreen = '#139e13'
const blue = '#1976d2'

/** svg object for a level in the game tree */
export function LevelIcon({ world, level, position, completed, unlocked }:
  { world: string,
    level: number,
    position: cytoscape.Position,
    completed: boolean,
    unlocked: boolean,
  }) {
  const gameId = React.useContext(GameIdContext)
  const difficulty = useSelector(selectDifficulty(gameId))
  const x = s * position.x + Math.sin(level * 2 * Math.PI / N) * (R + 1.2*r + 2.4*r*Math.floor((level - 1)/N))
  const y = s * position.y - Math.cos(level * 2 * Math.PI / N) * (R + 1.2*r + 2.4*r*Math.floor((level - 1)/N))
  const levelDisabled = (difficulty >= 2 && !(unlocked || completed))
  return (
    <Link to={levelDisabled ? '' : `/${gameId}/world/${world}/level/${level}`}
        className={`level${levelDisabled ? ' disabled' : ''}`}>
      <circle fill={completed ? lightgreen : unlocked? blue : grey} cx={x} cy={y} r={r} />
      <foreignObject className="level-title-wrapper" x={x} y={y}
          width={1.42*r} height={1.42*r} transform={"translate("+ -.71*r +","+ -.71*r +")"}>
        <div>
          <p className="level-title" style={{fontSize: Math.floor(r) + "px"}}>
            {level}
          </p>
        </div>
      </foreignObject>
    </Link>
  )
}

/** svg object of one world in the game tree */
export function WorldIcon({world, title, position, completedLevels, difficulty}:
  { world: string,
    title: string,
    position: cytoscape.Position,
    completedLevels: any,
    difficulty: number }) {

  // index `0` indicates that all prerequisites are completed
  let unlocked = completedLevels[0]
  // indices `1`-`n` indicate that the corresponding level is completed
  let completed = completedLevels.slice(1).every(Boolean)
  // select the first non-completed level
  let nextLevel: number = completedLevels.findIndex(c => !c)
  if (nextLevel <= 1) {
    // note: `findIndex` returns `-1` on failure, therefore the indices
    // `-1, 0, 1` indicate all that the introduction should be shown
    nextLevel = 0
  }
  let playable = difficulty <= 1 || completed || unlocked

  const gameId = React.useContext(GameIdContext)

  return <Link
      to={playable ? `/${gameId}/world/${world}/level/${nextLevel}` : ''}
      className={playable ? '' : 'disabled'}>
    <circle className="world-circle" cx={s*position.x} cy={s*position.y} r={R}
        fill={completed ? green : unlocked ? blue : grey}/>
    <foreignObject className="world-title-wrapper" x={s*position.x} y={s*position.y}
        width={1.42*R} height={1.42*R} transform={"translate("+ -.71*R +","+ -.71*R +")"}>
      <div className={unlocked && !completed ? "playable-world" : ''}>
        <p className="world-title" style={{fontSize: Math.floor(R/4) + "px"}}>
          {title ? title : world}
        </p>
      </div>
    </foreignObject>
  </Link>
}

/** svg object for a connection path between worlds in the game tree */
export function WorldPath({source, target, unlocked} : {source: any, target: any, unlocked: boolean}) {
  return <line x1={s*source.position.x} y1={s*source.position.y}
          x2={s*target.position.x} y2={s*target.position.y}
          stroke={unlocked ? green : lightgrey} strokeWidth={s}/>
}

/** Download a file containing `data` */
const downloadFile = ({ data, fileName, fileType } :
  { data: string
    fileName: string
    fileType: string}) => {
  const blob = new Blob([data], { type: fileType })
  const a = document.createElement('a')
  a.download = fileName
  a.href = window.URL.createObjectURL(blob)
  const clickEvt = new MouseEvent('click', {
    view: window,
    bubbles: true,
    cancelable: true,
  })
  a.dispatchEvent(clickEvt)
  a.remove()
}

/** The menu that is shown next to the world selection graph */
export function WelcomeMenu() {

  return <nav className="world-selection-menu">
    <Button inverted="false" title="back to games selection" to="/">
      <FontAwesomeIcon icon={faArrowLeft} />&nbsp;<FontAwesomeIcon icon={faGlobe} />
    </Button>

  </nav>
}

/** The menu that is shown next to the world selection graph */
function WorldSelectionMenu() {
  const [file, setFile] = React.useState<File>();

  const gameId = React.useContext(GameIdContext)
  const store = useStore()
  const difficulty = useSelector(selectDifficulty(gameId))


  /* state variables to toggle the pop-up menus */
  const [eraseMenu, setEraseMenu] = React.useState(false);
  const openEraseMenu = () => setEraseMenu(true);
  const closeEraseMenu = () => setEraseMenu(false);
  const [uploadMenu, setUploadMenu] = React.useState(false);
  const openUploadMenu = () => setUploadMenu(true);
  const closeUploadMenu = () => setUploadMenu(false);

  const gameProgress = useSelector(selectProgress(gameId))
  const dispatch = useAppDispatch()

  /** Download the current progress (i.e. what's saved in the browser store) */
  const downloadProgress = (e) => {
    e.preventDefault()
    downloadFile({
      data: JSON.stringify(gameProgress, null, 2),
      fileName: `lean4game-${gameId}-${new Date().toLocaleDateString()}.json`,
      fileType: 'text/json',
    })
  }

  const handleFileChange = (e) => {
    if (e.target.files) {
      setFile(e.target.files[0])
    }
  }

  /** Upload progress from a  */
  const uploadProgress = (e) => {
    if (!file) {return}
    const fileReader = new FileReader()
    fileReader.readAsText(file, "UTF-8")
    fileReader.onload = (e) => {
      const data = JSON.parse(e.target.result.toString()) as GameProgressState
      console.debug("Json Data", data)
      dispatch(loadProgress({game: gameId, data: data}))
    }
    closeUploadMenu()
  }

  const eraseProgress = () => {
    dispatch(deleteProgress({game: gameId}))
    closeEraseMenu()
  }

  const downloadAndErase = (e) => {
    downloadProgress(e)
    eraseProgress()
  }

  function label(x : number) {
    return x == 0 ? 'playground' : x == 1 ? 'explorer' : 'regular'
  }

  return <nav className="world-selection-menu">
    <Button onClick={downloadProgress} title="Download game progress" to=""><FontAwesomeIcon icon={faDownload} /></Button>
    <Button title="Load game progress from JSON" onClick={openUploadMenu} to=""><FontAwesomeIcon icon={faUpload} /></Button>
    <Button title="Clear game progress" to="" onClick={openEraseMenu}><FontAwesomeIcon icon={faEraser} /></Button>
    <div className="slider-wrap">
      <span className="difficulty-label">difficulty:</span>
      <Slider
        title="Difficulties:&#10;- regular: 🔐 levels, 🔐 tactics&#10;- explorer: 🔓 levels, 🔐 tactics&#10;- playground: 🔓 levels, 🔓 tactics"
        min={0} max={2}
        aria-label="Mode"
        defaultValue={difficulty}
        marks={[
          {value: 0, label: label(0)},
          {value: 1, label: label(1)},
          {value: 2, label: label(2)}
        ]}
        valueLabelFormat={label}
        getAriaValueText={label}
        valueLabelDisplay="auto"
        onChange={(ev, val: number) => {
          dispatch(changedDifficulty({game: gameId, difficulty: val}))
        }}
        ></Slider>

    </div>
    {eraseMenu?
      <div className="modal-wrapper">
        <div className="modal-backdrop" onClick={closeEraseMenu} />
        <div className="modal">
          <div className="codicon codicon-close modal-close" onClick={closeEraseMenu}></div>
          <h2>Delete Progress?</h2>

          <p>Do you want to delete your saved progress irreversibly?</p>
          <p>
            (This deletes your proofs and your collected inventory.
            Saves from other games are not deleted.)
          </p>

          <Button onClick={eraseProgress} to="">Delete</Button>
          <Button onClick={downloadAndErase} to="">Download & Delete</Button>
          <Button onClick={closeEraseMenu} to="">Cancel</Button>
        </div>
      </div> : null}
    {uploadMenu ?
      <div className="modal-wrapper">
        <div className="modal-backdrop" onClick={closeUploadMenu} />
        <div className="modal">
          <div className="codicon codicon-close modal-close" onClick={closeUploadMenu}></div>
          <h2>Upload Saved Progress</h2>

          <p>Select a JSON file with the saved game progress to load your progress.</p>

          <p><b>Warning:</b> This will delete your current game progress!
            Consider <a className="download-link" onClick={downloadProgress} >downloading your current progress</a> first!</p>

          <input type="file" onChange={handleFileChange}/>

          <Button to="" onClick={uploadProgress}>Load selected file</Button>
        </div>
      </div> : null}
  </nav>
}

export function computeWorldLayout(worlds) {

  let elements = []
  for (let id in worlds.nodes) {
    elements.push({ data: { id: id, title: worlds.nodes[id].title } })
  }
  for (let edge of worlds.edges) {
    elements.push({
      data: {
        id: edge[0] + " --edge-to--> " + edge[1],
        source: edge[0],
        target: edge[1]
      }
    })
  }

  const cy = cytoscape({
    container: null,
    elements,
    headless: true,
    styleEnabled: false
  })

  const layout = cy.layout({name: "klay", klay: {direction: "DOWN", nodePlacement: "LINEAR_SEGMENTS"}} as LayoutOptions).run()
  let nodes = {}
  cy.nodes().forEach((node, id) => {
    nodes[node.id()] = {
      position: node.position(),
      data: node.data()
    }
  })
  const bounds = cy.nodes().boundingBox()
  return { nodes, bounds }
}


export function WorldTreePanel({worlds, worldSize}:
  { worlds: any,
    worldSize: any}) {
  const gameId = React.useContext(GameIdContext)
  const difficulty = useSelector(selectDifficulty(gameId))

  const {nodes, bounds}: any = worlds ? computeWorldLayout(worlds) : {nodes: []}

  // scroll to playable world
  React.useEffect(() => {
    let elems = Array.from(document.getElementsByClassName("playable-world"))
    if (elems.length) {
      // it seems that the last element is the one furthest up in the tree
      // TODO: I think they appear in random order. Check there position and select the lowest one
      // of these positions to scroll to.
      let elem = elems[0]
      console.debug(`scrolling to ${elem.textContent}`)
      elem.scrollIntoView({block: "center"})
    }
  }, [worlds, worldSize])


  let svgElements = []

  // for each `worldId` as index, this contains a list of booleans with indices
  // 0, 1, …, n. Index `0` will be set to `false` if any dependency is not completely solved.
  // Indices `1, …, n` indicate if the corresponding level is completed
  var completed = {}

  if (worlds && worldSize) {
    // Fill `completed` with the level data.
    for (let worldId in nodes) {
      completed[worldId] = Array.from({ length: worldSize[worldId] + 1 }, (_, i) => {
        // index `0` starts off as `true` but can be set to `false` by any edge with non-completed source
        return i == 0 || selectCompleted(gameId, worldId, i)(store.getState())
      })
    }

    // draw all connecting paths
    for (let i in worlds.edges) {
      const edge = worlds.edges[i]
      let sourceCompleted = completed[edge[0]].slice(1).every(Boolean)
      // if the origin world is not completed, mark the target world as non-playable
      if (!sourceCompleted) {completed[edge[1]][0] = false}
      svgElements.push(
        <WorldPath source={nodes[edge[0]]} target={nodes[edge[1]]} unlocked={sourceCompleted}/>
      )
    }

    // draw the worlds and levels
    for (let worldId in nodes) {
      let position: cytoscape.Position = nodes[worldId].position
      svgElements.push(
        <WorldIcon world={worldId}
          title={nodes[worldId].data.title || worldId}
          position={position}
          completedLevels={completed[worldId]}
          difficulty={difficulty}
          key={`${gameId}-${worldId}`} />
      )
      for (let i = 1; i <= worldSize[worldId]; i++) {
        svgElements.push(
          <LevelIcon
            world={worldId}
            level={i}
            position={position}
            completed={completed[worldId][i]} unlocked={completed[worldId][i-1]}
            key={`${gameId}-${worldId}-${i}`} />
        )
      }
    }
  }

  let dx = bounds ? s*(bounds.x2 - bounds.x1) + 2*padding : null

  return <div className="column">
    <WorldSelectionMenu />
      <svg xmlns="http://www.w3.org/2000/svg" xmlnsXlink="http://www.w3.org/1999/xlink"
        width={bounds ? `${ds * dx}` : ''}
          viewBox={bounds ? `${s*bounds.x1 - padding} ${s*bounds.y1 - padding} ${dx} ${s*(bounds.y2 - bounds.y1) + 2 * padding}` : ''}
          className="world-selection"
        >
        {svgElements}
      </svg>
  </div>
  }
