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

cytoscape.use( klay );

import { Box, Typography, Button, CircularProgress, Grid } from '@mui/material';
import { LeanClient } from 'lean4web/client/src/editor/leanclient';

interface WelcomeProps {
  leanClient: null|LeanClient;
  setNbLevels: any;
  setTitle: any;
  startGame: any;
  setConclusion: any;
}

type infoResultType = {
  title: string,
  nb_levels: any[],
  conclusion: string
  worlds: {edges: string[][], nodes: string[]}
}

function Welcome({ leanClient, setNbLevels, setTitle, startGame, setConclusion }: WelcomeProps) {

  const [leanData, setLeanData] = useState<null|infoResultType>(null)
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

  useEffect(() => {
    if (!leanClient) return;

    const getInfo = async () => {
      await leanClient.start() // TODO: need a way to wait for start without restarting
      leanClient.sendRequest("info", {}).then((res: infoResultType) =>{
        console.log(res)
        setLeanData(res)
        setNbLevels(res.nb_levels)
        setTitle(res.title)
        document.title = res.title
        setConclusion(res.conclusion)
        drawWorlds(res.worlds)
      });
    }
    getInfo()
  }, [leanClient])

  let content
  if (leanData) {
    content = (<Box sx={{ m: 3 }}>
      <Typography variant="body1" component="div">
        <MathJax>
          <ReactMarkdown>{leanData["introduction"]}</ReactMarkdown>
        </MathJax>
      </Typography>
      <Box textAlign='center' sx={{ m: 5 }}>
        <Button onClick={startGame} variant="contained">Start rescue mission</Button>
      </Box>
    </Box>)
  } else {
    content = <Box display="flex" alignItems="center" justifyContent="center" sx={{ height: "calc(100vh - 64px)" }}><CircularProgress /></Box>
  }
  return <div>
    <div>{content}</div>
    <div ref={worldsRef} style={{"width": "100%","height": "50em"}} />
  </div>
}

export default Welcome
