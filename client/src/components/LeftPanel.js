import React, { useState, useEffect } from 'react';
import ReactMarkdown from 'react-markdown';
import { MathJax } from "better-react-mathjax";
import '@fontsource/roboto/300.css';
import '@fontsource/roboto/400.css';
import '@fontsource/roboto/500.css';
import '@fontsource/roboto/700.css';

import { Paper, Box, Typography, Accordion, AccordionSummary, AccordionDetails, Tabs, Tab } from '@mui/material';
import ExpandMoreIcon from '@mui/icons-material/ExpandMore';


function TacticDoc(props) {
	return (
		<Accordion>
			<AccordionSummary expandIcon={<ExpandMoreIcon />}>
				<Typography>{props.tactic.name}</Typography>
			</AccordionSummary>
			<AccordionDetails>
				<MathJax>
					<ReactMarkdown>{props.tactic.content}</ReactMarkdown>
				</MathJax>
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
				<MathJax>
					<ReactMarkdown>{lemma.content}</ReactMarkdown>
				</MathJax>
			</AccordionDetails>
		</Accordion>)
}

function LemmaDocs({ lemmas }) {
	const [categories, setCategories] = useState(new Map())
	const [curCategory, setCurCategory] = useState("")

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
		<Paper sx={{ px: 2, py: 1, mt: 2 }}>
			<Typography variant="h5">Inventory</Typography>
			<Box sx={{ borderBottom: 1, borderColor: 'divider' }}>
				<Tabs
					value={curCategory}
					aria-label="Categories" variant="scrollable" scrollButtons="auto">
					{(Array.from(categories)).map(([category, _]) => <Tab value={category} label={category} key={category} wrapped />)}
				</Tabs>
			</Box>
			{curCategory && categories.get(curCategory).map((lemma) => <LemmaDoc lemma={lemma} key={lemma.name} />)}
		</Paper>
	)
}

function LeftPanel({ spells, inventory }) {
	return (
		<Box>
			{spells.length > 0 &&
				<Paper sx={{ px: 2, py: 1 }}>
					<Typography variant="h5" sx={{ mb: 2 }}>Spell book</Typography>
					{spells.map((spell) => <TacticDoc key={spell.name} tactic={spell} />)}
				</Paper>}
			{inventory.length > 0 && <LemmaDocs lemmas={inventory} />}
		</Box>)
}

export default LeftPanel;
