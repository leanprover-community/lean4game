import * as React from 'react';
import { useState, useEffect, useRef } from 'react';
import './welcome.css'
import cytoscape, { LayoutOptions } from 'cytoscape'
import klay from 'cytoscape-klay';
import { useNavigate } from 'react-router-dom';
import { useSelector } from 'react-redux';


cytoscape.use( klay );

import { Box, Typography, CircularProgress } from '@mui/material';
import { useGetGameInfoQuery } from '../state/api';
import { Link } from 'react-router-dom';
import Markdown from './Markdown';
import { selectCompleted } from '../state/progress';
import { GameIdContext } from '../App';


function LevelIcon({ worldId, levelId, position }) {
  const gameId = React.useContext(GameIdContext)
  const completed = useSelector(selectCompleted(gameId, worldId,levelId))
  // TODO: relative positioning?
  return (
    <Link to={`/game/${gameId}/${worldId}/level/${levelId}`} key={`/game/${gameId}/world/${worldId}/level/${levelId}`}>
      <circle fill={completed ? "green" :"#aaa"} cx={position.x + Math.sin(levelId/5) * 9} cy={position.y - Math.cos(levelId/5) * 9} r="0.8" />
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

  const padding = 20

  const svgElements = []

  if (gameInfo.data) {
    for (let i in gameInfo.data.worlds.edges) {
      const edge = gameInfo.data.worlds.edges[i]
      svgElements.push(
        <line key={`pathway${i}`} x1={nodes[edge[0]].position.x} y1={nodes[edge[0]].position.y}
          x2={nodes[edge[1]].position.x} y2={nodes[edge[1]].position.y} stroke="#1976d2" strokeWidth="1"/>
      )
    }
    for (let id in nodes) {
      let position: cytoscape.Position = nodes[id].position

      svgElements.push(
        <Link key={`world${id}`} to={`/game/${gameId}/world/${id}/level/0`}>
          <circle className="world-circle" cx={position.x} cy={position.y} r="8" />
          <text className="world-name"
            x={position.x} y={position.y}>{nodes[id].data.title ? nodes[id].data.title : id}</text>
        </Link>
      )

      for (let i = 1; i <= gameInfo.data.worldSize[id]; i++) {
        svgElements.push(
          <LevelIcon position={position} worldId={id} levelId={i} />
        )
      }
    }
  }

  return <div>
  { gameInfo.isLoading?
    <Box display="flex" alignItems="center" justifyContent="center" sx={{ height: "calc(100vh - 64px)" }}><CircularProgress /></Box>
    :
    <div className="app-content">
      <Box sx={{ m: 3 }}>
        <Typography variant="body1" component="div">
          <Markdown>{gameInfo.data?.introduction}</Markdown>
        </Typography>
      </Box>
      <Box textAlign='center' sx={{ m: 5 }}>
        <svg xmlns="http://www.w3.org/2000/svg" xmlnsXlink="http://www.w3.org/1999/xlink" width="30%"
            viewBox={bounds ? `${bounds.x1 - padding} ${bounds.y1 - padding} ${bounds.x2 - bounds.x1 + 2 * padding} ${bounds.y2 - bounds.y1 + 2 * padding}` : ''}>
          {svgElements}
        </svg>
      </Box>
    </div>
  }

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
// TODO: Jon play around with graph layout

  const layout = cy.layout({name: "klay", klay: {direction: "DOWN"}} as LayoutOptions).run()
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
