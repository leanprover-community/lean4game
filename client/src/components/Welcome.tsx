import * as React from 'react';
import { useState, useEffect, useRef } from 'react';
import ReactMarkdown from 'react-markdown';
import { MathJax } from "better-react-mathjax";
import '@fontsource/roboto/300.css';
import '@fontsource/roboto/400.css';
import '@fontsource/roboto/500.css';
import '@fontsource/roboto/700.css';
import * as rpc from 'vscode-ws-jsonrpc';
import cytoscape from 'cytoscape'
import klay from 'cytoscape-klay';
import { useSelector, useDispatch } from 'react-redux'
import { fetchGame } from '../game/gameSlice'

cytoscape.use( klay );

import { Box, Typography, Button, CircularProgress, Grid } from '@mui/material';
import { LeanClient } from 'lean4web/client/src/editor/leanclient';
import { ConnectionContext } from '../connection';
import { useAppDispatch, useAppSelector } from '../hooks';

interface WelcomeProps {
  setNbLevels: any;
  startGame: any;
  setConclusion: any;
}

function Welcome({ setNbLevels, startGame, setConclusion }: WelcomeProps) {
  const dispatch = useAppDispatch()

  const worldsRef = useRef<HTMLDivElement>(null)

  const drawWorlds = (worlds) => {
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
    const layout : any = {name: "klay", klay: {direction: "DOWN"}}
    cytoscape({ container: worldsRef.current!, elements, layout,
      style: [ // the stylesheet for the graph
        {
          selector: 'node',
          style: {
            'background-color': '#666',
            'label': 'data(id)'
          }
        },

        {
          selector: 'edge',
          style: {
            'width': 3,
            'line-color': '#ccc',
            'target-arrow-color': '#ccc',
            'target-arrow-shape': 'triangle',
            'curve-style': 'bezier'
          }
        }
      ],
      userPanningEnabled: false,
      userZoomingEnabled: false,
      autoungrabify: true,
      autounselectify: true,
    })
  }

  useEffect(() => { dispatch(fetchGame); }, [])

  const worlds = useAppSelector(state => state.game.worlds)
  useEffect(() => { if (worlds) { drawWorlds(worlds); } }, [worlds])

  const title = useAppSelector(state => state.game.title)
  useEffect(() => { window.document.title = title }, [title])

  const introduction = useAppSelector(state => state.game.introduction)

  return <div>
  { introduction?// TODO: find a better way to mark loading state?
    <div>
      <Box sx={{ m: 3 }}>
        <Typography variant="body1" component="div">
          <MathJax>
            <ReactMarkdown>{introduction}</ReactMarkdown>
          </MathJax>
        </Typography>
      </Box>
      <Box textAlign='center' sx={{ m: 5 }}>
        <Button onClick={startGame} variant="contained">Start rescue mission</Button>
      </Box>
      <div ref={worldsRef} style={{"width": "100%","height": "50em"}} />
    </div>
    : <Box display="flex" alignItems="center" justifyContent="center" sx={{ height: "calc(100vh - 64px)" }}><CircularProgress /></Box>
  }

  </div>
}

export default Welcome
