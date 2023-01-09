import * as React from 'react';
import { useState, useEffect, useRef } from 'react';
import '@fontsource/roboto/300.css';
import '@fontsource/roboto/400.css';
import '@fontsource/roboto/500.css';
import '@fontsource/roboto/700.css';
import cytoscape, { LayoutOptions } from 'cytoscape'
import klay from 'cytoscape-klay';
import { Link as RouterLink, useNavigate } from 'react-router-dom';
import { useSelector } from 'react-redux';


cytoscape.use( klay );

import { Box, Typography, Button, CircularProgress, Grid, selectClasses } from '@mui/material';
import { useGetGameInfoQuery } from '../state/api';
import { Link } from 'react-router-dom';
import Markdown from './Markdown';
import { selectCompleted } from '../state/progress';


function LevelIcon({ worldId, levelId, position }) {
  const completed = useSelector(selectCompleted(worldId,levelId))
  // TODO: relative positioning?
  return (
    <Link to={`/world/${worldId}/level/${levelId}`} key={`/world/${worldId}/level/${levelId}`}>
      <circle fill={completed ? "green" :"#aaa"} cx={position.x + Math.sin(levelId/5) * 9} cy={position.y - Math.cos(levelId/5) * 9} r="0.8" />
    </Link>
  )
}

function Welcome() {
  const navigate = useNavigate();

  const gameInfo = useGetGameInfoQuery()

  const { nodes, bounds }: any = gameInfo.data ? computeWorldLayout(gameInfo.data?.worlds) : {nodes: []}

  useEffect(() => {
    if (gameInfo.data?.title) window.document.title = gameInfo.data.title
  }, [gameInfo.data?.title])

  const padding = 10

  const svgElements = []

  if (gameInfo.data) {
    for (let i in gameInfo.data.worlds.edges) {
      const edge = gameInfo.data.worlds.edges[i]
      svgElements.push(
        <line key={`pathway${i}`} x1={nodes[edge[0]].x} y1={nodes[edge[0]].y} x2={nodes[edge[1]].x} y2={nodes[edge[1]].y} stroke="#1976d2" strokeWidth="1"/>
      )
    }
    for (let id in nodes) {
      let position: cytoscape.Position = nodes[id]

      svgElements.push(
        <Link key={`world${id}`} to={`/world/${id}/level/1`}>
          <circle fill="#61DAFB" cx={position.x} cy={position.y} r="8" />
          <text style={{font: "italic 2px sans-serif",  textAnchor: "middle", dominantBaseline: "middle"} as any} x={position.x} y={position.y}>{id}</text>
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
    <div>
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
  for (let node of worlds.nodes) {
    elements.push({ data: { id: node } })
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

  const layout = cy.layout({name: "klay", klay: {direction: "DOWN"}} as LayoutOptions).run()
  let nodes = {}
  cy.nodes().forEach((node, id) => {
    nodes[node.id()] = node.position()
  })
  const bounds = cy.nodes().boundingBox()
  return { nodes, bounds }
}
