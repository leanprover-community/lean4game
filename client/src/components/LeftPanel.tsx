import * as React from 'react';
import { useState, useEffect } from 'react';
import ReactMarkdown from 'react-markdown';
import './inventory.css'

import { Paper, Box, Typography, Accordion, AccordionSummary, AccordionDetails, Tabs, Tab, Divider, Button, List, ListItem, ListItemButton, ListItemIcon, ListItemText } from '@mui/material';
import ExpandMoreIcon from '@mui/icons-material/ExpandMore';

import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faLock, faLockOpen, faBook, faHammer, faBan } from '@fortawesome/free-solid-svg-icons'
import Markdown from './Markdown';

function TacticDoc(props) {
  return (
    <Accordion>
      <AccordionSummary expandIcon={<ExpandMoreIcon />}>
        <Typography>{props.tactic.name}</Typography>
      </AccordionSummary>
      <AccordionDetails>
        <Markdown>{props.tactic.content}</Markdown>
      </AccordionDetails>
    </Accordion>)
}

function LemmaDoc({ lemma }) {
  return (
    <Accordion>
      <AccordionSummary expandIcon={<ExpandMoreIcon />}>
        <Typography>{lemma.userName}</Typography>
      </AccordionSummary>
      <AccordionDetails>
        <Markdown>{lemma.content}</Markdown>
      </AccordionDetails>
    </Accordion>)
}

function LemmaDocs({ lemmas }) {
  const [categories, setCategories] = useState(new Map())
  const [curCategory, setCurCategory] = useState("")

  const changeTab = (event: React.SyntheticEvent, newValue : string) => {
    setCurCategory(newValue);
  };

  useEffect(() => {
    const cats = new Map()
    lemmas.forEach(function (item) {
      const category = item.category
      cats.set(category, (cats.get(category) || []).concat([item]))
    });
    setCategories(cats)
    setCurCategory(cats.keys().next().value)
  }, [lemmas]);

  return (
    <div>
      <Box sx={{ borderBottom: 1, borderColor: 'divider' }}>
        <Tabs
          value={curCategory}
          onChange={changeTab}
          aria-label="Categories" variant="scrollable" scrollButtons="auto">
          {(Array.from(categories)).map(([category, _]) => <Tab value={category} label={category} key={category} wrapped />)}
        </Tabs>
      </Box>
      {curCategory && categories.get(curCategory).map((lemma) => <LemmaDoc lemma={lemma} key={lemma.name} />)}
    </div>)
}

function LeftPanel({ spells, inventory, showSidePanel, setShowSidePanel }) {

  return (
    <>
    <div className="tactic-inventory">
      {  ["rfl", "tauto", "trivial", "simp", "left", "right", "assumption", "constructor"].map ((tac) => {
        const locked = Math.random() > 0.5
        const disabled = Math.random() > 0.5
        const icon = locked ? faLock : disabled ? faBan : faLockOpen
        const className = locked ? "locked" : disabled ? "disabled" : ""
        return <div className={`tactic ${className}`}><FontAwesomeIcon icon={icon} />&nbsp;{tac}</div>
    })}
    </div>
    <List className="side">
      <ListItem key="tactics" disablePadding sx={{ display: 'block' }}>
        <ListItemButton sx={{ minHeight: 48, justifyContent: showSidePanel ? 'initial' : 'center', px: 2.5 }} onClick={() => setShowSidePanel(true)}>
          <ListItemIcon sx={{minWidth: 0, mr: showSidePanel ? 3 : 'auto', justifyContent: 'center' }}>
            <FontAwesomeIcon icon={faHammer}></FontAwesomeIcon>
          </ListItemIcon>
          <ListItemText primary="Known Tactics" sx={{ display: showSidePanel ? null : "none" }} />
        </ListItemButton>
        {spells && spells.length > 0 &&
          <Paper sx={{ px: 2, py: 1, display: showSidePanel ? null : "none" }} elevation={0} >
            {spells.map((spell) => <TacticDoc key={spell.name} tactic={spell} />)}
          </Paper>}
      </ListItem>
      <ListItem key="lemmas" disablePadding sx={{ display: 'block' }}>
        <ListItemButton sx={{ minHeight: 48, justifyContent: showSidePanel ? 'initial' : 'center', px: 2.5 }} >
          <ListItemIcon sx={{minWidth: 0, mr: showSidePanel ? 3 : 'auto', justifyContent: 'center' }}>
            <FontAwesomeIcon icon={faBook}></FontAwesomeIcon>
          </ListItemIcon>
          <ListItemText primary="Known Lemmas" sx={{ display: showSidePanel ? null : "none" }} />
        </ListItemButton>
        {inventory && inventory.length > 0 &&
          <Paper sx={{ px: 2, py: 1, mt: 2, display: showSidePanel ? null : "none" }} elevation={0} >
            <LemmaDocs lemmas={inventory} />
          </Paper>}
      </ListItem>
    </List>
    </>
  )
}

export default LeftPanel;
