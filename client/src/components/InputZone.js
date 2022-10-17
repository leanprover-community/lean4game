import React, { useEffect, useState } from 'react';
import '@fontsource/roboto/300.css';
import '@fontsource/roboto/400.css';
import '@fontsource/roboto/500.css';
import '@fontsource/roboto/700.css';

import { Typography, Button, Paper, TextField, List, ListItem } from '@mui/material';


function InputZone({ index, history, messageOpen, setMessageOpen, completed, sendTactic, nbLevels, loadNextLevel, errors, lastTactic, undo, finishGame }) {
  const [curInput, setCurInput] = useState("")

  const inputRef = React.createRef()
  const nextRef = React.createRef()

  function handleCurInputChange(evt) { setCurInput(evt.target.value) }

  function showPrevMessage() { setMessageOpen(true) }

  useEffect(() => {
    if (!messageOpen && !completed) inputRef.current.focus()
    if (!messageOpen && completed && index < nbLevels) nextRef.current.focus()
    if (!messageOpen && completed && index === nbLevels) finishGame()
  }, [messageOpen, inputRef, nextRef, completed, finishGame, index, nbLevels])

  async function submitForm(evt) {
    evt.preventDefault(); // prevent app reloading on form submission
    await sendTactic(curInput)
    setCurInput("");
  }

  return (
    <Paper sx={{
        height: "100%", pt: 1, pl: 3, pr: 3, pb: 1,
        justifyContent: "space-between", alignItems: "center", textAlign: "center"
      }}
      elevation={5}>
      <Typography variant="h5">Invocation zone</Typography>
      <List dense={true}>
        {history.map((item, idx) => <ListItem key={idx}>{item}</ListItem>)}
      </List>
      <form onSubmit={submitForm}>
        <TextField
          id="outlined-input"
          label="Invocation"
          autoFocus={true}
          inputRef={inputRef}
          value={curInput}
          onChange={handleCurInputChange}
        />
        <br />
        <Button type="submit" variant="contained" sx={{ mt: 2 }} disabled={errors.length > 0 || completed || curInput.trim() === ""} disableFocusRipple>Cast spell</Button>
        <br />
        <Button variant="text" onClick={undo} sx={{ ml: 3, mt: 2, mb: 2 }} disabled={lastTactic === "" ? true : false || completed}>Undo</Button>
        {!messageOpen && <Button variant="text" onClick={showPrevMessage} sx={{ ml: 3, mt: 2, mb: 2 }}>See previous message</Button>}
        <br />
        {completed && index < nbLevels && <Button variant="contained" ref={nextRef} onClick={loadNextLevel} sx={{ ml: 3, mt: 2, mb: 2 }} disableFocusRipple>Go to Next Level</Button>}
      </form>
    </Paper>)
}

export default InputZone
