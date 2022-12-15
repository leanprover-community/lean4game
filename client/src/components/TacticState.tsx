import * as React from 'react';
import '@fontsource/roboto/300.css';
import '@fontsource/roboto/400.css';
import '@fontsource/roboto/500.css';
import '@fontsource/roboto/700.css';

import List from '@mui/material/List';
import ListItem from '@mui/material/ListItem';
import { Paper, Box, Typography, Alert, FormControlLabel, FormGroup, Switch, Collapse } from '@mui/material';
import { Accordion, AccordionSummary, AccordionDetails, Divider } from '@mui/material';
import ExpandMoreIcon from '@mui/icons-material/ExpandMore';

import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faArrowPointer } from '@fortawesome/free-solid-svg-icons'
import Markdown from './Markdown';

// TODO: Dead variables (x✝) are not displayed correctly.

function Goal({ goal }) {

  const [showHints, setShowHints] = React.useState(false);

  const handleHintsChange = () => {
    setShowHints((prev) => !prev);
  };

  const hasObject = typeof goal.objects === "object" && goal.objects.length > 0
  const hasAssumption = typeof goal.assumptions === "object" && goal.assumptions.length > 0
  const openMessages = typeof goal.messages === "object" ? goal.messages.filter((msg) => ! msg.spoiler) : []
  const hints = typeof goal.messages === "object" ? goal.messages.filter((msg) => msg.spoiler) : []
  const hasHints = hints.length > 0
  return (
    <Box sx={{ pl: 2 }}>
      {hasObject && <Box><Typography>Objects</Typography>
        <List>
          {goal.objects.map((item) =>
            <ListItem key={item.userName}>
              <Typography color="primary" sx={{ mr: 1 }}>{item.userName}</Typography> :
              <Typography color="secondary" sx={{ ml: 1 }}>{item.type}</Typography>
            </ListItem>)}
        </List></Box>}
      {hasAssumption && <Box><Typography>Assumptions</Typography>
        <List>
          {goal.assumptions.map((item) => <ListItem key={item}><Typography color="primary" sx={{ mr: 1 }}>{item.userName}</Typography> :
            <Typography color="secondary" sx={{ ml: 1 }}>{item.type}</Typography></ListItem>)}
        </List></Box>}
      <Typography>Prove:</Typography>
      <Typography color="primary" sx={{ ml: 2 }}>{goal.goal}</Typography>
      {openMessages.map((message) => <Alert severity="info" sx={{ mt: 1 }}><Markdown>{message.message}</Markdown></Alert>)}
      {hasHints &&
        <FormControlLabel
          control={<Switch checked={showHints} onChange={handleHintsChange} />}
          label="More Help?"
        />}
        {hints.map((hint) => <Collapse in={showHints}><Alert severity="info" sx={{ mt: 1 }}><Markdown>{hint.message}</Markdown></Alert></Collapse>)}
    </Box>)
}

/* Function to display a goal that is not the main goal. */
function OtherGoal({ goal }) {

  const hasObject = typeof goal.objects === "object" && goal.objects.length > 0
  const hasAssumption = typeof goal.assumptions === "object" && goal.assumptions.length > 0

  return (
    <Accordion>
      <AccordionSummary expandIcon={<ExpandMoreIcon />}>
        <Typography color="primary" sx={{ ml: 0 }}>⊢ {goal.goal}</Typography>
      </AccordionSummary>
      <AccordionDetails sx={{ backgroundColor: "aliceblue" }}>
        {hasObject &&
          <Box>
            <Typography>Objects</Typography>
            <List>
              {goal.objects.map((item) =>
                <ListItem key={item.userName}>
                  <Typography color="primary" sx={{ mr: 1 }}>{item.userName}</Typography> :
                  <Typography color="secondary" sx={{ ml: 1 }}>{item.type}</Typography>
                </ListItem>)}
            </List>
          </Box>}
        {hasAssumption &&
          <Box>
            <Typography>Assumptions</Typography>
            <List>
              {goal.assumptions.map((item) =>
                <ListItem key={item}>
                  <Typography color="primary" sx={{ mr: 1 }}>{item.userName}</Typography> :
                  <Typography color="secondary" sx={{ ml: 1 }}>{item.type}</Typography>
                </ListItem>)}
            </List>
          </Box>}
        <Typography>Prove:</Typography>
        <Typography color="primary" sx={{ ml: 2 }}>{goal.goal}</Typography>
      </AccordionDetails>
    </Accordion>)
}

function TacticState({ goals, diagnostics, completed }) {
  const hasError = typeof diagnostics === "object" && diagnostics.length > 0
  const hasGoal = goals !== null && goals.length > 0
  const hasManyGoal = hasGoal && goals.length > 1
  return (
    <Box sx={{ height: "100%" }}>
      {hasGoal &&
        <Paper sx={{ pt: 1, pl: 2, pr: 3, pb: 1, height: "100%" }}>
          <Typography variant="h5">Main Goal
            (at <FontAwesomeIcon icon={faArrowPointer}></FontAwesomeIcon>)
          </Typography>
          <Goal goal={goals[0]} />
        </Paper>}
      {!(hasGoal || completed) &&
        <Typography variant="h6">
          No goals
          (at <FontAwesomeIcon icon={faArrowPointer}></FontAwesomeIcon>)
        </Typography>}
      {completed && <Typography variant="h6">Level completed ! 🎉</Typography>}
      {hasError &&
        <Paper sx={{ pt: 1, pl: 2, pr: 3, pb: 1, height: "100%" }}>
          <Typography variant="h5" sx={{ mb: 2 }}>Lean says</Typography>
          {diagnostics.map(({severity, message}) =>
            <Alert severity={{1: "error", 2:"warning", 3:"info", 4:"success"}[severity]} sx={{ mt: 1 }}>{message}</Alert>
            // TODO: When does Lean give severity=4? Had colour `gray` before. Make custom theme for that
          )}
        </Paper>}
      {hasManyGoal && <Paper sx={{ pt: 1, pl: 2, pr: 3, pb: 1, mt: 1 }}>
        <Typography variant="h5" sx={{ mb: 2 }}>Further Goals</Typography>
        {goals.slice(1).map((goal, index) => <Paper><OtherGoal key={index} goal={goal} /></Paper>)}
      </Paper>}
    </Box>
  )
}

export default TacticState
