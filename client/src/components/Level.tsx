import * as React from 'react';
import { useEffect, useState } from 'react';
import '@fontsource/roboto/300.css';
import '@fontsource/roboto/400.css';
import '@fontsource/roboto/500.css';
import '@fontsource/roboto/700.css';

import Grid from '@mui/material/Unstable_Grid2';

import LeftPanel from './LeftPanel';
import InputZone from './InputZone';
import Message from './Message';
import TacticState from './TacticState';



function Level({ sendJsonMessage, lastMessage, lastJsonMessage, nbLevels, level, setCurLevel, setLevelTitle, setFinished }) {
	const [index, setIndex] = useState(level) // Level number
	const [tacticDocs, setTacticDocs] = useState([])
	const [lemmaDocs, setLemmaDocs] = useState([])

	const [leanData, setLeanData] = useState({goals: []})
	const [history, setHistory] = useState([])
	const [lastTactic, setLastTactic] = useState("")
	const [errors, setErrors] = useState([])

	const [message, setMessage] = useState("")
	const [messageOpen, setMessageOpen] = useState(false)


	const [completed, setCompleted] = useState(false)

	// The next function will be called when the level changes
	useEffect(() => {
		sendJsonMessage({ "loadLevel": level });
	}, [level, sendJsonMessage])

	// The next function will be called when a message arrives or the level title changes
	useEffect(() => {
		console.log(lastMessage)
		console.log(lastJsonMessage)
		if ("nb_levels" in lastJsonMessage) { return } // this is an old message from starting the game
		const data = lastJsonMessage;
		if ("title" in data) { // This is the level metadata coming in
			setLevelTitle("Level " + data["index"] + ": " + data["title"])
			setIndex(parseInt(data["index"]))
			setTacticDocs(data["tactics"])
			setLemmaDocs(data["lemmas"])
		}

		if (data["message"] !== "" && data.errors.length === 0) {
			setMessage(data["message"])
			setMessageOpen(true)
		}
		setLeanData(data);
		setErrors(data.errors);
		if (data.goals.length === 0 && data.errors.length === 0) {
			setCompleted(true)
		}

	}, [lastJsonMessage, lastMessage, setLevelTitle])


	function sendTactic(input) {
		sendJsonMessage({ "runTactic": input });
		setLastTactic(input);
		setHistory(history.concat([input]));
	}

	function undo() {
		if (errors.length === 0) {
			sendJsonMessage('undo');
		}
		if (history.length > 1) {
			setLastTactic(history[history.length - 1]);
		} else {
			setLastTactic("");
		};
		setErrors([]);
		setHistory(history.slice(0, -1));
	}

	function loadNextLevel() {
		setCompleted(false)
		setHistory([])
		setCurLevel(index + 1)
	}

	function closeMessage() {
		setMessageOpen(false)
	}

	function finishGame() {
		setLevelTitle("")
		setFinished(true)
	}

	return (
		<Grid container sx={{ mt: 3, ml: 1, mr: 1 }} columnSpacing={{ xs: 1, sm: 2, md: 3 }}>
			<Grid xs={4}>
				<LeftPanel spells={tacticDocs} inventory={lemmaDocs} />
			</Grid>
			<Grid xs={4}>
				<InputZone index={index} history={history} messageOpen={messageOpen} setMessageOpen={setMessageOpen} completed={completed} sendTactic={sendTactic} nbLevels={nbLevels} loadNextLevel={loadNextLevel}
					errors={errors} lastTactic={lastTactic} undo={undo} finishGame={finishGame} />
				<Message isOpen={messageOpen} content={message} close={closeMessage} />
			</Grid>
			<Grid xs={4}>
				<TacticState goals={leanData.goals} errors={errors} lastTactic={lastTactic} completed={completed} />
			</Grid>
		</Grid>
	)
}

export default Level