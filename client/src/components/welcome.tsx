import * as React from 'react';
import { useState, useEffect, useRef } from 'react';
import { Link } from 'react-router-dom';
import { useNavigate } from 'react-router-dom';
import { useSelector } from 'react-redux';
import Split from 'react-split'
import { Box, Typography, CircularProgress, Slider } from '@mui/material';
import cytoscape, { LayoutOptions } from 'cytoscape'
import klay from 'cytoscape-klay';
import './welcome.css'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faGlobe, faBook, faHome, faCircleInfo, faArrowRight, faArrowLeft, faShield, faRotateLeft } from '@fortawesome/free-solid-svg-icons'
import { GameIdContext } from '../app';
import { selectCompleted, selectDifficulty } from '../state/progress';
import { useGetGameInfoQuery, useLoadInventoryOverviewQuery } from '../state/api';
import Markdown from './markdown';
import WorldSelectionMenu, { WelcomeMenu } from './world_selection_menu';
import {PrivacyPolicy} from './privacy_policy';
import { Button } from './button';
import { Documentation, Inventory } from './inventory';
import { store } from '../state/store';
import { useWindowDimensions } from '../window_width';
import { MobileContext } from './infoview/context';

cytoscape.use( klay );

const N = 18              // max number of levels per world
const R = 64              // radius of a world
const r = 12              // radius of a level
const s = 10              // global scale
const padding = R + 2*r   // padding of the graphic (on a different scale)
const ds = .75            // scale the resulting svg image

function LevelIcon({ worldId, levelId, position, completed, available }) {
  const gameId = React.useContext(GameIdContext)

  const difficulty = useSelector(selectDifficulty(gameId))

  const x = s * position.x + Math.sin(levelId * 2 * Math.PI / N) * (R + 1.2*r + 2.4*r*Math.floor((levelId - 1)/N))
  const y = s * position.y - Math.cos(levelId * 2 * Math.PI / N) * (R + 1.2*r + 2.4*r*Math.floor((levelId - 1)/N))

  let levelDisabled = (difficulty >= 2 && !(available || completed))

  // TODO: relative positioning?
  return (
    <Link to={levelDisabled ? '' : `/${gameId}/world/${worldId}/level/${levelId}`}
        className={`level${levelDisabled ? ' disabled' : ''}`}>
      <circle fill={completed ? "#139e13" : available? "#1976d2" : "#999"} cx={x} cy={y} r={r} />
      <foreignObject className="level-title-wrapper" x={x} y={y}
              width={1.42*r} height={1.42*r} transform={"translate("+ -.71*r +","+ -.71*r +")"}>
            <div>
              <p className="level-title" style={{fontSize: Math.floor(r) + "px"}}>
               {levelId}
              </p>
            </div>
          </foreignObject>
    </Link>
  )
}

function Welcome() {
  const navigate = useNavigate();

  /** Only for mobile layout */
  const [pageNumber, setPageNumber] = useState(0)

  const gameId = React.useContext(GameIdContext)
  const gameInfo = useGetGameInfoQuery({game: gameId})

  const {mobile} = React.useContext(MobileContext)

  const inventory = useLoadInventoryOverviewQuery({game: gameId})

  const difficulty = useSelector(selectDifficulty(gameId))

  // When clicking on an inventory item, the inventory is overlayed by the item's doc.
  // If this state is set to a pair `(name, type)` then the according doc will be open.
  const [inventoryDoc, setInventoryDoc] = useState<{name: string, type: string}>(null)

  // Open the doc of the clicked inventory item
  function openInventoryDoc(name, type) {
    setInventoryDoc({name, type})
  }

  // Set `inventoryDoc` to `null` to close the doc
  const closeInventoryDoc = () => setInventoryDoc(null);

  const { nodes, bounds }: any = gameInfo.data ? computeWorldLayout(gameInfo.data?.worlds) : {nodes: []}

  useEffect(() => {
    if (gameInfo.data?.title) {
      window.document.title = gameInfo.data.title
    }
  }, [gameInfo.data?.title])

  // Scroll to playable world
  useEffect(() => {
    let elems = Array.from(document.getElementsByClassName("playable-world"))
    if (elems.length) {
      // It seems that the last element is the one furthest up in the tree
      // TODO: I think they appear in random order. Check there position and select the lowest one
      // of these positions to scroll to.
      let elem = elems[0]
      console.debug(`scrolling to ${elem.textContent}`)
      elem.scrollIntoView({block: "center"})
    }
  }, [gameInfo])

  const svgElements = []

  // For each `worldId` as index, this contains a list of booleans with indices
  // 0, 1, …, n. Index `0` will be set to `false` if any dependency is not completely solved.
  // Indices `1, …, n` indicate if the corresponding level is completed
  var completed = {}

  if (gameInfo.data) {

    // Fill `completed` with the level data.
    for (let worldId in nodes) {
      let position: cytoscape.Position = nodes[worldId].position
      let state = store.getState()

      completed[worldId] = Array.from({ length: gameInfo.data.worldSize[worldId] + 1 }, (_, i) => {
        // Index `0` might be set to `false` in the loop over the edges
        if (!i) {return true}
        return selectCompleted(gameId, worldId, i)(state)
      })
    }

    for (let i in gameInfo.data.worlds.edges) {
      const edge = gameInfo.data.worlds.edges[i]

      // If the origin world is not completed, mark the target world as non-playable
      let unlocked = completed[edge[0]].slice(1).every(Boolean)
      if (!unlocked) {completed[edge[1]][0] = false}

      // Draw the connection edges
      svgElements.push(
        <line key={`pathway${i}`} x1={s*nodes[edge[0]].position.x} y1={s*nodes[edge[0]].position.y}
          x2={s*nodes[edge[1]].position.x} y2={s*nodes[edge[1]].position.y}
          stroke={unlocked ? "green" : "#bbb"} strokeWidth={s}/>
      )
    }

    for (let worldId in nodes) {
      // Draw the level bubbles
      let position: cytoscape.Position = nodes[worldId].position
      for (let i = 1; i <= gameInfo.data.worldSize[worldId]; i++) {
        svgElements.push(
          <LevelIcon
            key={`/${gameId}/world/${worldId}/level/${i}`}
            position={position} worldId={worldId} levelId={i}
            completed={completed[worldId][i]} available={completed[worldId][i-1]}/>
        )
      }

      let worldUnlocked = completed[worldId][0]
      let worldCompleted = completed[worldId].slice(1).every(Boolean)

      // This selects the first uncompleted level
      let nextLevel: number = completed[worldId].findIndex(c => !c)
      if (nextLevel <= 1) {
        // This uses the fact that `findIndex` returns `-1` if it does not find an uncompleted entry
        // so `-1, 0, 1` are all the indices where we want to show the introduction.
        nextLevel = 0
      }

      let worldDisabled = (difficulty >= 2 && !(worldUnlocked || worldCompleted))

      // Draw the worlds
      svgElements.push(
        <Link key={`world${worldId}`}
            to={worldDisabled ? '' : `/${gameId}/world/${worldId}/level/${nextLevel}`}
            className={worldDisabled ? 'disabled' : ''}>
          <circle className="world-circle" cx={s*position.x} cy={s*position.y} r={R}
              fill={worldCompleted ? "green" : worldUnlocked ? "#1976d2": "#999"}/>
          <foreignObject className="world-title-wrapper" x={s*position.x} y={s*position.y}
              width={1.42*R} height={1.42*R} transform={"translate("+ -.71*R +","+ -.71*R +")"}>
            <div className={worldUnlocked && !worldCompleted ? "playable-world" : ''}>
              <p className="world-title" style={{fontSize: Math.floor(R/4) + "px"}}>
                {nodes[worldId].data.title ? nodes[worldId].data.title : worldId}
              </p>
            </div>
          </foreignObject>
        </Link>
      )
    }
  }

  let dx = bounds ? s*(bounds.x2 - bounds.x1) + 2*padding : null

  // TODO: Pack the three columns into components, so we dont need to
  // copy them for mobile layout
  return <div className="app-content">
  { gameInfo.isLoading?
    <Box display="flex" alignItems="center" justifyContent="center" sx={{ height: "calc(100vh - 64px)" }}>
      <CircularProgress />
    </Box>
    : mobile ?
      (pageNumber == 0 ?
        <div className="column">
          <div className="mobile-nav">
            <Button className="btn btn-previous" to="/" title="back to games selection">
              <FontAwesomeIcon icon={faArrowLeft} />&nbsp;<FontAwesomeIcon icon={faGlobe} />
            </Button>
            <Button className="btn btn-next" to=""
                title="world tree" onClick={() => {setPageNumber(1)}}>
              Game&nbsp;<FontAwesomeIcon icon={faArrowRight}/>
            </Button>
          </div>
          <Typography variant="body1" component="div" className="welcome-text">
            <Markdown>{gameInfo.data?.introduction}</Markdown>
          </Typography>
        </div>
        : pageNumber == 1 ?
        <div className="column">
          <div className="mobile-nav">
            <Button className="btn btn-previous" to=""
                title="back to introduction" onClick={() => {setPageNumber(0)}}>
              <FontAwesomeIcon icon={faArrowLeft}/>&nbsp;Intro
            </Button>
            <Button className="btn btn-next" to=""
                title="show inventory" onClick={() => {setPageNumber(2)}}>
              <FontAwesomeIcon icon={faBook}/>&nbsp;<FontAwesomeIcon icon={faArrowRight}/>
            </Button>
          </div>
          <WorldSelectionMenu />
            <svg xmlns="http://www.w3.org/2000/svg" xmlnsXlink="http://www.w3.org/1999/xlink"
              width={bounds ? `${ds * dx}` : ''}
                viewBox={bounds ? `${s*bounds.x1 - padding} ${s*bounds.y1 - padding} ${dx} ${s*(bounds.y2 - bounds.y1) + 2 * padding}` : ''}
                className="world-selection"
              >
              {svgElements}
            </svg>
        </div>
        :
        <div className="inventory-panel">
          <div className="mobile-nav">
            <Button className="btn btn-previous" to=""
                title="world tree" onClick={() => {setPageNumber(1)}}>
              <FontAwesomeIcon icon={faArrowLeft} />&nbsp;Game
            </Button>
          </div>
          {<>
            {inventoryDoc ?
              <Documentation name={inventoryDoc.name} type={inventoryDoc.type} handleClose={closeInventoryDoc}/>
              :
              <Inventory levelInfo={inventory.data} openDoc={openInventoryDoc} enableAll={true}/>
            }
          </>}
        </div>
      )
      :
      <Split className="welcome" minSize={0} snapOffset={200}  sizes={[40, 35, 25]}>
        <div className="column">
          <Typography variant="body1" component="div" className="welcome-text">
            <WelcomeMenu />
            <Markdown>{gameInfo.data?.introduction}</Markdown>
          </Typography>
        </div>
        <div className="column">
          <WorldSelectionMenu />
            <svg xmlns="http://www.w3.org/2000/svg" xmlnsXlink="http://www.w3.org/1999/xlink"
              width={bounds ? `${ds * dx}` : ''}
                viewBox={bounds ? `${s*bounds.x1 - padding} ${s*bounds.y1 - padding} ${dx} ${s*(bounds.y2 - bounds.y1) + 2 * padding}` : ''}
                className="world-selection"
              >
              {svgElements}
            </svg>
        </div>
        <div className="inventory-panel">
          {<>
            {inventoryDoc ?
              <Documentation name={inventoryDoc.name} type={inventoryDoc.type} handleClose={closeInventoryDoc}/>
              :
              <Inventory levelInfo={inventory.data} openDoc={openInventoryDoc} enableAll={true}/>
            }
          </>}
        </div>
      </Split>
  }
  <PrivacyPolicy />
  </div>
}

export default Welcome

function computeWorldLayout(worlds) {

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
