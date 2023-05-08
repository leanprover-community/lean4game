import * as React from 'react';
import { useState, useEffect, useRef } from 'react';
import './welcome.css'
import cytoscape, { LayoutOptions } from 'cytoscape'
import klay from 'cytoscape-klay';
import { useNavigate } from 'react-router-dom';
import { useSelector } from 'react-redux';
import Split from 'react-split'

import GameMenu from './GameMenu';
import {PrivacyPolicy} from './PrivacyPolicy';

cytoscape.use( klay );

import { Box, Typography, CircularProgress } from '@mui/material';
import { useGetGameInfoQuery } from '../state/api';
import { Link } from 'react-router-dom';
import Markdown from './Markdown';
import { selectCompleted } from '../state/progress';
import { GameIdContext } from '../App';
import { Button } from './Button';

import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faDownload, faUpload, faEraser } from '@fortawesome/free-solid-svg-icons'


const N = 24          // max number of levels per world
const R = 800         // radius of a world
const r = 110          // radius of a level
const s = 100         // global scale
const padding = 2000  // padding of the graphic (on a different scale)

function LevelIcon({ worldId, levelId, position }) {
  const gameId = React.useContext(GameIdContext)
  const completed = useSelector(selectCompleted(gameId, worldId,levelId))

  const x = s * position.x + Math.sin(levelId * 2 * Math.PI / N) * (R + 1.2*r + 2*Math.floor((levelId - 1)/N))
  const y = s * position.y - Math.cos(levelId * 2 * Math.PI / N) * (R + 1.2*r + 2*Math.floor((levelId - 1)/N))

  // TODO: relative positioning?
  return (
    <Link to={`/game/${gameId}/world/${worldId}/level/${levelId}`}>
      <circle fill={completed ? "green" :"#999"} cx={x} cy={y} r={r} />
    </Link>
  )
}

function Welcome() {
  const navigate = useNavigate();

  const gameId = React.useContext(GameIdContext)
  const gameInfo = useGetGameInfoQuery({game: gameId})

  const { nodes, bounds }: any = gameInfo.data ? computeWorldLayout(gameInfo.data?.worlds) : {nodes: []}

  useEffect(() => {
    if (gameInfo.data?.title) {
      window.document.title = gameInfo.data.title
    }
  }, [gameInfo.data?.title])

  const svgElements = []

  if (gameInfo.data) {
    for (let i in gameInfo.data.worlds.edges) {
      const edge = gameInfo.data.worlds.edges[i]
      svgElements.push(
        <line key={`pathway${i}`} x1={s*nodes[edge[0]].position.x} y1={s*nodes[edge[0]].position.y}
          x2={s*nodes[edge[1]].position.x} y2={s*nodes[edge[1]].position.y} stroke="#1976d2" strokeWidth={s}/>
      )
    }

    for (let id in nodes) {
      let position: cytoscape.Position = nodes[id].position

      for (let i = 1; i <= gameInfo.data.worldSize[id]; i++) {
        svgElements.push(
          <LevelIcon
            key={`/game/${gameId}/world/${id}/level/${i}`}
            position={position} worldId={id} levelId={i} />
        )
      }

      svgElements.push(
        <Link key={`world${id}`} to={`/game/${gameId}/world/${id}/level/0`}>
          <circle className="world-circle" cx={s*position.x} cy={s*position.y} r={R}
              fill="#1976d2"/>
          <foreignObject className="world-title-wrapper" x={s*position.x} y={s*position.y}
              width={1.42*R} height={1.42*R} transform={"translate("+ -.71*R +","+ -.71*R +")"}>
            <div>
              <p className="world-title" style={{fontSize: Math.floor(R/4) + "px"}}>
                {nodes[id].data.title ? nodes[id].data.title : id}
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
    <Split className="welcome" minSize={200} sizes={[70, 30]}>
      <div className="column">
        <Typography variant="body1" component="div" className="welcome-text">
          <Markdown>{gameInfo.data?.introduction}</Markdown>
        </Typography>
      </div>
      <div className="column">
        <GameMenu />
        <Box textAlign='center' sx={{ m: 5 }}>
          <svg xmlns="http://www.w3.org/2000/svg" xmlnsXlink="http://www.w3.org/1999/xlink"
              viewBox={bounds ? `${s*bounds.x1 - padding} ${s*bounds.y1 - padding} ${s*bounds.x2 - s*bounds.x1 + 2 * padding} ${s*bounds.y2 - s*bounds.y1 + 2 * padding}` : ''}>
            {svgElements}
          </svg>
        </Box>
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
