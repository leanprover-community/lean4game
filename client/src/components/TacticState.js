import React from 'react';
import '@fontsource/roboto/300.css';
import '@fontsource/roboto/400.css';
import '@fontsource/roboto/500.css';
import '@fontsource/roboto/700.css';

import List from '@mui/material/List';
import ListItem from '@mui/material/ListItem';
import { Paper, Box, Typography } from '@mui/material';

const errorRegex = /<stdin>:1:(?<col>[^:]*): (?<msg>.*)/;

function Goal({ goal }) {
	const hasObject = typeof goal.objects === "object" && goal.objects.length > 0
	const hasAssumption = typeof goal.assumptions === "object" && goal.assumptions.length > 0
	return (
		<Box sx={{ pl: 2 }}>
			{hasObject && <Box><Typography variant="h7">Objects</Typography>
				<List>
					{goal.objects.map((item) =>
						<ListItem key={item[0]}>
							<Typography color="primary" sx={{ mr: 1 }}>{item[0]}</Typography> :
							<Typography color="secondary" sx={{ ml: 1 }}>{item[1]}</Typography>
						</ListItem>)}
				</List></Box>}
			{hasAssumption && <Box><Typography variant="h7">Assumptions</Typography>
				<List>
					{goal.assumptions.map((item) => <ListItem key={item}><Typography color="primary" sx={{ mr: 1 }}>{item[0]}</Typography> :
						<Typography color="secondary" sx={{ ml: 1 }}>{item[1]}</Typography></ListItem>)}
				</List></Box>}
			<Typography variant="h7">Prove:</Typography>
			<Typography color="primary" sx={{ ml: 2 }}>{goal.goal}</Typography>
		</Box>)
}

function TacticState({ goals, errors, lastTactic, completed }) {
	const hasError = typeof errors === "object" && errors.length > 0
	const hasGoal = typeof goals === "object" && goals.length > 0
	const hasManyGoal = hasGoal && goals.length > 1
	var col = ""
	var msg = ""
	if (hasError) {
		const m = errors[0].match(errorRegex)
		if (m) {
			col = `Column ${m.groups.col}: `
			msg = m.groups.msg
		} else {
			msg = errors[0]
			if (msg === "Unrecognized tactic") { msg = "Unknown spell!" }
		}
	}
	return (
		<Box sx={{ height: "100%" }}>
			{hasGoal && <Paper sx={{ pt: 1, pl: 2, pr: 3, pb: 1, height: "100%" }}><Typography variant="h5">Current goal</Typography> <Goal goal={goals[0]} /></Paper>}
			{completed && <Typography variant="h6">Level completed ! 🎉</Typography>}
			{hasError && <Paper sx={{ pt: 1, pl: 2, pr: 3, pb: 1, height: "100%" }}><Typography variant="h5" color="error">Spell invocation failed</Typography>
				<Typography sx={{ my: 1 }}>{lastTactic}</Typography>
				<Typography component="pre" sx={{ my: 1 }}>{col}{msg}</Typography>
				<Typography>Use the undo button to go back to a sane state.</Typography>
				</Paper>}
			{hasManyGoal && <Paper sx={{ pt: 1, pl: 2, pr: 3, pb: 1, mt: 1 }}>
				<Typography variant="h6" sx={{ mb: 2 }}>Other goals</Typography>
				{goals.slice(1).map((goal, index) => <Paper><Goal key={index} goal={goal} /></Paper>)}
			</Paper>}
		</Box>
	)
}

export default TacticState