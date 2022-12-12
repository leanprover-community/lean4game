import * as React from 'react';
import { useState, useEffect, useRef } from 'react';
import ReactMarkdown from 'react-markdown';
import { MathJax } from "better-react-mathjax";
import '@fontsource/roboto/300.css';
import '@fontsource/roboto/400.css';
import '@fontsource/roboto/500.css';
import '@fontsource/roboto/700.css';
import cytoscape from 'cytoscape'
import klay from 'cytoscape-klay';
import { Link as RouterLink, useNavigate } from 'react-router-dom';


cytoscape.use( klay );

import { Box, Typography, Button, CircularProgress, Grid } from '@mui/material';
import { useGetGameInfoQuery } from '../game/api';


function Welcome() {
  const navigate = useNavigate();

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
    const cy = cytoscape({ container: worldsRef.current!, elements, layout,
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

    cy.on('click', 'node', function(evt){
      navigate(`/world/${this.id()}/level/1`);
    });
  }

  const gameInfo = useGetGameInfoQuery()

  useEffect(() => {
    if (gameInfo.data?.worlds) { drawWorlds(gameInfo.data.worlds); }
  }, [gameInfo.data?.worlds])

  useEffect(() => {
    if (gameInfo.data?.title) window.document.title = gameInfo.data.title
  }, [gameInfo.data?.title])

  return <div>
  { gameInfo.isLoading?
    <Box display="flex" alignItems="center" justifyContent="center" sx={{ height: "calc(100vh - 64px)" }}><CircularProgress /></Box>
    :
    <div>
      <Box sx={{ m: 3 }}>
        <Typography variant="body1" component="div">
          <MathJax>
            <ReactMarkdown>{gameInfo.data.introduction}</ReactMarkdown>
          </MathJax>
        </Typography>
      </Box>
      <Box textAlign='center' sx={{ m: 5 }}>
        <Button component={RouterLink} to="/world/Logic/level/1" variant="contained">Start rescue mission</Button>
      </Box>
      <div ref={worldsRef} style={{"width": "100%","height": "50em"}} />
    </div>
  }

  </div>
}

export default Welcome
