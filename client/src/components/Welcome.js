import React, { useState, useEffect } from 'react';
import ReactMarkdown from 'react-markdown';
import { MathJax } from "better-react-mathjax";
import '@fontsource/roboto/300.css';
import '@fontsource/roboto/400.css';
import '@fontsource/roboto/500.css';
import '@fontsource/roboto/700.css';

import { Box, Typography, Button, CircularProgress, Grid } from '@mui/material';


function Welcome({ sendJsonMessage, lastJsonMessage, setNbLevels, setTitle, startGame, setConclusion }) {

	const [leanData, setLeanData] = useState({})

	// Will run at the very beginning
	useEffect(() => {
		sendJsonMessage('info')
	}, [sendJsonMessage])

	// Will run when a Json message arrives
	useEffect(() => {
		if (lastJsonMessage != null && lastJsonMessage.hasOwnProperty("nb_levels")) {
			setLeanData(lastJsonMessage)
			setNbLevels(lastJsonMessage.nb_levels)
			setTitle(lastJsonMessage.title)
			document.title = lastJsonMessage.title
			setConclusion(lastJsonMessage.conclusion)
		}
	}, [lastJsonMessage, setNbLevels, setTitle, setConclusion])

	let content
	if ("introduction" in leanData) {
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
