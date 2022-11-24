import * as React from 'react';
import { useState, useEffect } from 'react';
import ReactMarkdown from 'react-markdown';
import { MathJax } from "better-react-mathjax";
import '@fontsource/roboto/300.css';
import '@fontsource/roboto/400.css';
import '@fontsource/roboto/500.css';
import '@fontsource/roboto/700.css';
import * as rpc from 'vscode-ws-jsonrpc';

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
}

function Welcome({ leanClient, setNbLevels, setTitle, startGame, setConclusion }: WelcomeProps) {

  const [leanData, setLeanData] = useState<null|infoResultType>(null)

  useEffect(() => {
    if (!leanClient) return;

    const getInfo = async () => {
      await leanClient.start() // TODO: need a way to wait for start without restarting
      leanClient.sendRequest("info", "hello").then((res: infoResultType) =>{
        setLeanData(res)
        setNbLevels(res.nb_levels)
        setTitle(res.title)
        document.title = res.title
        setConclusion(res.conclusion)
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
  return <Grid container direction="row" justifyContent="center" alignItems="center">
    <Grid item xs={12} sm={6}>{content}</Grid>
  </Grid>
}

export default Welcome
