import * as React from 'react';
import { useState, useEffect, useRef } from 'react';
import { Link } from 'react-router-dom';
import { useNavigate } from 'react-router-dom';
import { useSelector } from 'react-redux';
import Split from 'react-split'
import { Box, Typography, CircularProgress } from '@mui/material';
import cytoscape, { LayoutOptions } from 'cytoscape'
import klay from 'cytoscape-klay';
import './welcome.css'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faGlobe, faHome, faCircleInfo, faArrowRight, faArrowLeft, faShield, faRotateLeft } from '@fortawesome/free-solid-svg-icons'
import { GameIdContext } from '../app';
import { selectCompleted } from '../state/progress';
import { useGetGameInfoQuery, useLoadInventoryOverviewQuery } from '../state/api';
import Markdown from './markdown';
import WorldSelectionMenu from './world_selection_menu';
import {PrivacyPolicy} from './privacy_policy';
import { Button } from './button';
import { Documentation, Inventory } from './inventory';
import { store } from '../state/store';

cytoscape.use( klay );

const N = 18          // max number of levels per world
const R = 800         // radius of a world
const r = 160          // radius of a level
const s = 120         // global scale
const padding = 2000  // padding of the graphic (on a different scale)

function LevelIcon({ worldId, levelId, position, completed, available }) {
  const gameId = React.useContext(GameIdContext)

  const x = s * position.x + Math.sin(levelId * 2 * Math.PI / N) * (R + 1.2*r + 2.4*r*Math.floor((levelId - 1)/N))
  const y = s * position.y - Math.cos(levelId * 2 * Math.PI / N) * (R + 1.2*r + 2.4*r*Math.floor((levelId - 1)/N))

  // TODO: relative positioning?
  return (
    <Link to={`/${gameId}/world/${worldId}/level/${levelId}`}>
      <circle fill={completed ? "#139e13" : available? "#1976d2" : "#999"} cx={x} cy={y} r={r} />
    </Link>
  )
}

function Welcome() {
  const navigate = useNavigate();

  const gameId = React.useContext(GameIdContext)
  const gameInfo = useGetGameInfoQuery({game: gameId})

  const inventory = useLoadInventoryOverviewQuery({game: gameId})

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

      // Draw the worlds
      let worldUnlocked = completed[worldId][0]
      let worldCompleted = completed[worldId].slice(1).every(Boolean)
      svgElements.push(
        <Link key={`world${worldId}`} to={`/${gameId}/world/${worldId}/level/0`}>
          <circle className="world-circle" cx={s*position.x} cy={s*position.y} r={R}
              fill={worldCompleted ? "green" : worldUnlocked ? "#1976d2": "#999"}/>
          <foreignObject className="world-title-wrapper" x={s*position.x} y={s*position.y}
              width={1.42*R} height={1.42*R} transform={"translate("+ -.71*R +","+ -.71*R +")"}>
            <div>
              <p className="world-title" style={{fontSize: Math.floor(R/4) + "px"}}>
                {nodes[worldId].data.title ? nodes[worldId].data.title : worldId}
              </p>
            </div>
          </foreignObject>
        </Link>
      )
    }
  }

  return <div className="app-content ">
  { gameInfo.isLoading?
    <Box display="flex" alignItems="center" justifyContent="center" sx={{ height: "calc(100vh - 64px)" }}>
      <CircularProgress />
    </Box>
    :
    <Split className="welcome" minSize={200} sizes={[40, 35, 25]}>
      <div className="column">
        <Typography variant="body1" component="div" className="welcome-text">
          <Button inverted="false" title="back to games selection" to="/">
            <FontAwesomeIcon icon={faArrowLeft} />&nbsp;<FontAwesomeIcon icon={faGlobe} />
          </Button>
          <Markdown>{gameInfo.data?.introduction}</Markdown>
        </Typography>
      </div>
      <div className="column">
        <WorldSelectionMenu />
        <Box textAlign='center' sx={{ m: 5 }}>
          <svg xmlns="http://www.w3.org/2000/svg" xmlnsXlink="http://www.w3.org/1999/xlink"
              viewBox={bounds ? `${s*bounds.x1 - padding} ${s*bounds.y1 - padding} ${s*bounds.x2 - s*bounds.x1 + 2 * padding} ${s*bounds.y2 - s*bounds.y1 + 2 * padding}` : ''}>
            {svgElements}
          </svg>
        </Box>
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
