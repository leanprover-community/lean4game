import * as React from 'react';
import { useEffect, useState, useRef } from 'react';
import '@fontsource/roboto/300.css';
import '@fontsource/roboto/400.css';
import '@fontsource/roboto/500.css';
import '@fontsource/roboto/700.css';
import { Link as RouterLink } from 'react-router-dom';
import { Box, Button, CircularProgress, FormControlLabel, FormGroup, Switch, IconButton } from '@mui/material';
import MuiDrawer from '@mui/material/Drawer';
import Grid from '@mui/material/Unstable_Grid2';
import LeftPanel from './LeftPanel';
import { LeanTaskGutter } from 'lean4web/client/src/editor/taskgutter';
import { AbbreviationProvider } from 'lean4web/client/src/editor/abbreviation/AbbreviationProvider';
import { AbbreviationRewriter } from 'lean4web/client/src/editor/abbreviation/rewriter/AbbreviationRewriter';
import { InfoProvider } from 'lean4web/client/src/editor/infoview';
import 'lean4web/client/src/editor/infoview.css'
import { renderInfoview } from '@leanprover/infoview'
import * as monaco from 'monaco-editor/esm/vs/editor/editor.api.js'
import './level.css'
import { ConnectionContext, useLeanClient } from '../connection';
import Infoview from './Infoview';
import { useParams } from 'react-router-dom';
import { useGetGameInfoQuery, useLoadLevelQuery } from '../state/api';
import { codeEdited, selectCode } from '../state/progress';
import { useAppDispatch } from '../hooks';
import { useSelector } from 'react-redux';

import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faUpload, faArrowRotateRight, faChevronLeft, faChevronRight, faBook, faDownload } from '@fortawesome/free-solid-svg-icons'

import { styled, useTheme, Theme, CSSObject } from '@mui/material/styles';
import { AppBarProps as MuiAppBarProps } from '@mui/material/AppBar';
import Divider from '@mui/material/Divider';
import Markdown from './Markdown';
import { SetTitleContext } from '../App';



/** Drawer Test */
const drawerWidth = 400; /* TODO: This width is hard-coded. Fix me. */

const openedMixin = (theme: Theme): CSSObject => ({
  width: drawerWidth,
  transition: theme.transitions.create('width', {
    easing: theme.transitions.easing.sharp,
    duration: theme.transitions.duration.enteringScreen,
  }),
  overflowX: 'hidden',
});

const closedMixin = (theme: Theme): CSSObject => ({
  transition: theme.transitions.create('width', {
    easing: theme.transitions.easing.sharp,
    duration: theme.transitions.duration.leavingScreen,
  }),
  overflowX: 'hidden',
  width: `calc(${theme.spacing(7)} + 1px)`,
  [theme.breakpoints.up('sm')]: {
    width: `calc(${theme.spacing(8)} + 1px)`,
  },
});

const DrawerHeader = styled('div')(({ theme }) => ({
  display: 'flex',
  alignItems: 'center',
  justifyContent: 'flex-end',
  padding: theme.spacing(0, 1),
  // necessary for content to be below app bar
  ...theme.mixins.toolbar,
}));

interface AppBarProps extends MuiAppBarProps {
  open?: boolean;
}

const Drawer = styled(MuiDrawer, { shouldForwardProp: (prop) => prop !== 'open' })(
  ({ theme, open }) => ({
    width: drawerWidth,
    flexShrink: 0,
    whiteSpace: 'nowrap',
    boxSizing: 'border-box',
    ...(open && {
      ...openedMixin(theme),
      '& .MuiDrawer-paper': openedMixin(theme),
    }),
    ...(!open && {
      ...closedMixin(theme),
      '& .MuiDrawer-paper': closedMixin(theme),
    }),
  }),
);

/** End Drawer Test */



function Level() {

  const params = useParams();
  const levelId = parseInt(params.levelId)
  const worldId = params.worldId

  const codeviewRef = useRef<HTMLDivElement>(null)
  const infoviewRef = useRef<HTMLDivElement>(null)
  const messagePanelRef = useRef<HTMLDivElement>(null)

  const [showSidePanel, setShowSidePanel] = useState(true)

  const toggleSidePanel = () => {
    setShowSidePanel(!showSidePanel)
  }

  const theme = useTheme();

  useEffect(() => {
    // Scroll to top when loading a new level
    messagePanelRef.current!.scrollTo(0,0)
  }, [levelId])

  const connection = React.useContext(ConnectionContext)

  const gameInfo = useGetGameInfoQuery()

  const level = useLoadLevelQuery({world: worldId, level: levelId})

  const dispatch = useAppDispatch()

  const onDidChangeContent = (code) => {
    dispatch(codeEdited({world: worldId, level: levelId, code}))
  }

  const initialCode = useSelector(selectCode(worldId, levelId))

  const {editor, infoProvider} =
    useLevelEditor(worldId, levelId, codeviewRef, initialCode, onDidChangeContent)

  const {setTitle, setSubtitle} = React.useContext(SetTitleContext);

  useEffect(() => {
    setTitle(`World: ${worldId}`)
  }, [worldId])

  useEffect(() => {
    setSubtitle(`Level ${levelId}: ${level?.data?.title}`)
  }, [level?.data?.title])

  return <>
    <Box style={level.isLoading ? null : {display: "none"}} display="flex" alignItems="center" justifyContent="center" sx={{ height: "calc(100vh - 64px)" }}><CircularProgress /></Box>
    <Box style={level.isLoading ? {display: "none"} : null} display="flex" className="level" sx={{ mt: 0, ml: 0, mr: 0 }} >
      <Drawer variant="permanent" open={showSidePanel} className="doc-panel">
        <DrawerHeader>
        </DrawerHeader>
        <Divider />
        <IconButton onClick={toggleSidePanel}>
          <FontAwesomeIcon icon={showSidePanel ? faChevronLeft : faChevronRight}></FontAwesomeIcon>
        </IconButton>
          <LeftPanel spells={level?.data?.tactics} inventory={level?.data?.lemmas} showSidePanel={showSidePanel} setShowSidePanel={setShowSidePanel} />
      </Drawer>
      <Grid container columnSpacing={{ xs: 1, sm: 2, md: 3 }} sx={{ flexGrow: 1, p: 3 }} className="main-grid">
        <Grid xs={8} className="main-panel">
          <div ref={messagePanelRef} className="message-panel">
            <Markdown>{level?.data?.introduction}</Markdown>
          </div>
          <div className="exercise">
            <h4>Aufgabe:</h4>
            <Markdown>{level?.data?.descrText}</Markdown>
            <div className="statement"><code>{level?.data?.descrFormat}</code></div>
            <div ref={codeviewRef} className="codeview"></div>
          </div>
        </Grid>
        <Grid xs={4} className="info-panel">

          <Button disabled={levelId <= 1} component={RouterLink} to={`/world/${worldId}/level/${levelId - 1}`} sx={{ ml: 3, mt: 2, mb: 2 }} disableFocusRipple>Previous Level</Button>
          <Button disabled={levelId >= gameInfo.data?.worldSize[worldId]} component={RouterLink} to={`/world/${worldId}/level/${levelId + 1}`} sx={{ ml: 3, mt: 2, mb: 2 }} disableFocusRipple>Next Level</Button>

          <Infoview key={worldId + "/Level" + levelId} leanClient={connection.getLeanClient()} editor={editor} editorApi={infoProvider?.getApi()} />
        </Grid>
      </Grid>
    </Box>
    </>
}

export default Level


function useLevelEditor(worldId: string, levelId: number, codeviewRef, initialCode, onDidChangeContent) {

  const connection = React.useContext(ConnectionContext)

  const [editor, setEditor] = useState<monaco.editor.IStandaloneCodeEditor|null>(null)
  const [infoProvider, setInfoProvider] = useState<null|InfoProvider>(null)

  // Create Editor
  useEffect(() => {
    const editor = monaco.editor.create(codeviewRef.current!, {
      glyphMargin: true,
      lightbulb: {
        enabled: true
      },
      unicodeHighlight: {
          ambiguousCharacters: false,
      },
      automaticLayout: true,
      minimap: {
        enabled: false
      },
      lineNumbersMinChars: 3,
      'semanticHighlighting.enabled': true,
      theme: 'vs-code-theme-converted'
    })

    const infoProvider = new InfoProvider(connection.getLeanClient())
console.log()
    setEditor(editor)
    setInfoProvider(infoProvider)

    return () => { editor.setModel(null); infoProvider.dispose(); editor.dispose() }
  }, [])

  const {leanClient, leanClientStarted} = useLeanClient()

  // Create model when level changes
  useEffect(() => {
    if (editor && leanClientStarted) {

      const uri = monaco.Uri.parse(`file:///${worldId}/${levelId}`)
      let model = monaco.editor.getModel(uri)
      if (!model) {
        model = monaco.editor.createModel(initialCode, 'lean4', uri)
        model.onDidChangeContent(() => onDidChangeContent(model.getValue()))
      }
      editor.setModel(model)
      const taskGutter = new LeanTaskGutter(infoProvider.client, editor)
      const abbrevRewriter = new AbbreviationRewriter(new AbbreviationProvider(), model, editor)

      return () => { abbrevRewriter.dispose(); taskGutter.dispose(); model.dispose() }
    }
  }, [editor, levelId, connection, leanClientStarted])

  return {editor, infoProvider}
}
