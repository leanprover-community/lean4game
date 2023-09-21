/**
 * @fileOverview Define the menu displayed with the tree of worlds on the welcome page
*/
import * as React from 'react'
import { Link } from 'react-router-dom'
import { useStore, useSelector } from 'react-redux'
import { Slider } from '@mui/material'
import cytoscape, { LayoutOptions } from 'cytoscape'
import klay from 'cytoscape-klay'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faDownload, faUpload, faEraser, faGlobe, faArrowLeft } from '@fortawesome/free-solid-svg-icons'

import { GameIdContext } from '../app'
import { useAppDispatch } from '../hooks'
import { deleteProgress, selectProgress, loadProgress, GameProgressState,
  selectDifficulty, changedDifficulty, selectCompleted } from '../state/progress'
import { store } from '../state/store'
import { Button } from './button'

import './world_tree.css'

// Settings for the world tree
cytoscape.use( klay )

const r = 16              // radius of a level
const s = 10              // global scale
const lineWidth = 10      //
const ds = .75  // scale the resulting svg image

const NMIN = 5   // min. worldsize
const NLABEL = 9 // max. world size to display label below the world
const NMAX = 16  // max. world size. Level icons start spiraling out if the world has more levels.

// colours
const grey = '#999'
const lightgrey = '#bbb'
const green = 'green' // 118a11?
const lightgreen = '#139e13'
const blue = '#1976d2'
const darkgrey = '#868686'
const darkgreen = '#0e770e'
const darkblue = '#1667b8'


/** svg object for a level in the game tree */
export function LevelIcon({ world, level, position, completed, unlocked, worldSize }:
  { world: string,
    level: number,
    position: cytoscape.Position,
    completed: boolean,
    unlocked: boolean,
    worldSize: number
  }) {

  const N = Math.max(worldSize, NMIN)

  // divide circle into `N+2` equal pieces
  const beta = 2 * Math.PI / Math.min(N+2, (NMAX+1))

  // We want distance between two level icons to be `2.2*r`, therefore:
  // Sinus-Satz: (1.1*r) / sin(β/2) = R / sin(π/2)
  let R = 1.1 * r / Math.sin(beta/2)

  const gameId = React.useContext(GameIdContext)
  const difficulty = useSelector(selectDifficulty(gameId))
  const levelDisabled = (difficulty >= 2 && !(unlocked || completed))

  /** In the spiral, the angle `β` should decrease to avoid big gaps between levels.
   * This is a simplified function, which has little mathematical foundation, but
   * works fine in tests up to `N=30`.
   */
  function betaSpiral(level) {
    return 2 * Math.PI / ((NMAX+1) + Math.max(0, (level-2)) / (NMAX+1))
  }

  const x = N < (NMAX+1) ?
    // normal case
    s * position.x + Math.sin(level * beta) * R :
    // spiraling case
    s * position.x + Math.sin(level * betaSpiral(level)) * (R + 2*r*(level-1)/(NMAX+1))
  const y = N < (NMAX+1) ?
    // normal case
    s * position.y - Math.cos(level * beta) * R :
    // spiraling case
    s * position.y - Math.cos(level * betaSpiral(level)) * (R + 2*r*(level-1)/(NMAX+1))

  return (
    <Link to={levelDisabled ? '' : `/${gameId}/world/${world}/level/${level == 1 ? 0 : level}`}
        className={`level${levelDisabled ? ' disabled' : ''}`}>
      <circle fill={completed ? lightgreen : unlocked? blue : lightgrey} cx={x} cy={y} r={r} />
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
export function WorldIcon({world, title, position, completedLevels, difficulty, worldSize}:
  { world: string,
    title: string,
    position: cytoscape.Position,
    completedLevels: any,
    difficulty: number,
    worldSize: number
  }) {

  // See level icons. Match radius computed there minus `1.2*r`
  const N = Math.max(worldSize, NMIN)
  const betaHalf = Math.PI / Math.min(N+2, (NMAX + 1))
  let R = 1.1 * r / Math.sin(betaHalf) - 1.2 * r

  // Offset for the labels for small worlds
  let labelOffset = R + 2.5 * r

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
    {worldSize > NLABEL ?
      // Label for large worlds
      <foreignObject className="world-title-wrapper" x={s*position.x} y={s*position.y}
          width={1.42*R} height={1.42*R} transform={"translate("+ -.71*R +","+ -.71*R +")"}>
        <div className={unlocked && !completed ? "playable-world" : ''}>
          <p className="world-title" style={{fontSize: Math.floor(R/4) + "px"}}>
            {title ? title : world}
          </p>
        </div>
      </foreignObject>
      :
      // Label for small worlds
      <foreignObject x={s*position.x - 75} y={s*position.y + labelOffset}
          width='150px' height='2em' style={{overflow: 'visible'}}
          >
        <div className='world-label' style={{backgroundColor: completed ? darkgreen : unlocked ? darkblue : darkgrey}}>
          <p className='world-title'>
            {title ? title : world}
          </p>
        </div>
      </foreignObject>}
  </Link>
}

/** svg object for a connection path between worlds in the game tree */
export function WorldPath({source, target, unlocked} : {source: any, target: any, unlocked: boolean}) {
  return <line x1={s*source.position.x} y1={s*source.position.y}
          x2={s*target.position.x} y2={s*target.position.y}
          stroke={unlocked ? green : grey} strokeWidth={lineWidth} />
}

/** Download a file containing `data` */
export const downloadFile = ({ data, fileName, fileType } :
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
export function WorldSelectionMenu() {
  const gameId = React.useContext(GameIdContext)
  const difficulty = useSelector(selectDifficulty(gameId))
  const dispatch = useAppDispatch()

  function label(x : number) {
    return x == 0 ? 'none' : x == 1 ? 'relaxed' : 'regular'
  }

  return <nav className="world-selection-menu">
    <div className="slider-wrap">
      <span className="difficulty-label">Game Rules</span>
      <Slider
        orientation="vertical"
        title="Game Rules:&#10;- regular: 🔐 levels, 🔐 tactics&#10;- relaxed: 🔓 levels, 🔐 tactics&#10;- none: 🔓 levels, 🔓 tactics"
        min={0} max={2}
        aria-label="Game Rules"
        defaultValue={difficulty}
        marks={[
          {value: 0, label: label(0)},
          {value: 1, label: label(1)},
          {value: 2, label: label(2)}
        ]}
        valueLabelFormat={label}
        getAriaValueText={label}
        valueLabelDisplay="off"
        onChange={(ev, val: number) => {
          dispatch(changedDifficulty({game: gameId, difficulty: val}))
        }}
        ></Slider>
    </div>
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

  cy.layout({name: "klay", klay: {direction: "DOWN", nodePlacement: "LINEAR_SEGMENTS"}} as LayoutOptions).run()

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
      // TODO: I think they appear in random order. Check their position and select the lowest one
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
        <WorldPath key={`path_${edge[0]}-->${edge[1]}`}
          source={nodes[edge[0]]} target={nodes[edge[1]]} unlocked={sourceCompleted}/>
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
          key={`${gameId}-${worldId}`}
          worldSize={worldSize[worldId]}
        />
      )

      for (let i = 1; i <= worldSize[worldId]; i++) {
        svgElements.push(
          <LevelIcon
            world={worldId}
            level={i}
            position={position}
            completed={completed[worldId][i]}
            unlocked={completed[worldId][i-1]}
            key={`${gameId}-${worldId}-${i}`}
            worldSize={worldSize[worldId]}
          />
        )
      }
    }
  }

  // See `LevelIcon` for calculation of the radius. Use the max. radius for calculating the padding
  // TODO: Is there a way to determine padding according to the drawn objects?
  let R = 1.1 * r / Math.sin(Math.PI / (NMAX+1))
  const padding = R + 2.1*r

  let dx = bounds ? s*(bounds.x2 - bounds.x1) + 2*padding : null

  return <div className="column">
      <WorldSelectionMenu />
      <svg xmlns="http://www.w3.org/2000/svg" xmlnsXlink="http://www.w3.org/1999/xlink"
          width={bounds ? `${ds * dx}` : ''}
          viewBox={bounds ? `${s*bounds.x1 - padding} ${s*bounds.y1 - padding} ${dx} ${s*(bounds.y2 - bounds.y1) + 2 * padding}` : ''}
          className="world-selection" >
        {svgElements}
      </svg>
  </div>
}
