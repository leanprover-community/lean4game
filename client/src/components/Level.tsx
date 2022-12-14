import * as React from 'react';
import { useEffect, useState, useRef } from 'react';
import '@fontsource/roboto/300.css';
import '@fontsource/roboto/400.css';
import '@fontsource/roboto/500.css';
import '@fontsource/roboto/700.css';
import ReactMarkdown from 'react-markdown';
import { MathJax } from "better-react-mathjax";
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
import { ConnectionContext } from '../connection';
import Infoview from './Infoview';
import { useParams } from 'react-router-dom';
import { useLoadLevelQuery } from '../game/api';
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faUpload, faArrowRotateRight, faChevronLeft, faChevronRight, faBook, faDownload } from '@fortawesome/free-solid-svg-icons'

import { styled, useTheme, Theme, CSSObject } from '@mui/material/styles';
import MuiAppBar, { AppBarProps as MuiAppBarProps } from '@mui/material/AppBar';
import Toolbar from '@mui/material/Toolbar';
import List from '@mui/material/List';
import CssBaseline from '@mui/material/CssBaseline';
import Typography from '@mui/material/Typography';
import Divider from '@mui/material/Divider';
import MenuIcon from '@mui/icons-material/Menu';
import ChevronLeftIcon from '@mui/icons-material/ChevronLeft';
import ChevronRightIcon from '@mui/icons-material/ChevronRight';
import ListItem from '@mui/material/ListItem';
import ListItemButton from '@mui/material/ListItemButton';
import ListItemIcon from '@mui/material/ListItemIcon';
import ListItemText from '@mui/material/ListItemText';
import InboxIcon from '@mui/icons-material/MoveToInbox';
import MailIcon from '@mui/icons-material/Mail';


/** Drawer Test */
const drawerWidth = 400;

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

  const [expertInfoview, setExpertInfoview] = useState(false)

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

  const level = useLoadLevelQuery({world: worldId, level: levelId})
  const {editor, infoProvider} = useLevelEditor(worldId, levelId, codeviewRef, infoviewRef)

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
            <MathJax><ReactMarkdown>{level?.data?.introduction}</ReactMarkdown></MathJax>
          </div>
          <div className="exercise">
            <h4>Aufgabe:</h4>
            <MathJax><ReactMarkdown>{level?.data?.descrText}</ReactMarkdown></MathJax>
            <div className="statement"><code>{level?.data?.descrFormat}</code></div>
            <div ref={codeviewRef} className="codeview"></div>
          </div>
        </Grid>
        <Grid xs={4} className="info-panel">

          <Button disabled={levelId <= 1} component={RouterLink} to={`/world/${worldId}/level/${levelId - 1}`} sx={{ ml: 3, mt: 2, mb: 2 }} disableFocusRipple>Previous Level</Button>
          <Button disabled={false} component={RouterLink} to={`/world/${worldId}/level/${levelId + 1}`} sx={{ ml: 3, mt: 2, mb: 2 }} disableFocusRipple>Next Level</Button>

          <div style={{display: expertInfoview ? 'block' : 'none' }} ref={infoviewRef} className="infoview vscode-light"></div>
          <div style={{display: expertInfoview ? 'none' : 'block' }}>
            <Infoview leanClient={connection.getLeanClient()} editor={editor} editorApi={infoProvider?.getApi()} />
          </div>
          <FormGroup>
            <FormControlLabel onChange={() => { setExpertInfoview(!expertInfoview) }} control={<Switch />} label="Expert mode" />
          </FormGroup>
        </Grid>
      </Grid>
    </Box>
    </>
}

export default Level


function useLevelEditor(worldId: string, levelId: number, codeviewRef, infoviewRef) {

  const connection = React.useContext(ConnectionContext)

  const [editor, setEditor] = useState<monaco.editor.IStandaloneCodeEditor|null>(null)
  const [infoProvider, setInfoProvider] = useState<null|InfoProvider>(null)
  const [infoviewApi, setInfoviewApi] = useState(null)

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
    const div: HTMLElement = infoviewRef.current!
    const infoviewApi = renderInfoview(infoProvider.getApi(), div)

    setEditor(editor)
    setInfoProvider(infoProvider)
    setInfoviewApi(infoviewApi)

    return () => { editor.setModel(null); infoProvider.dispose(); }
  }, [])

  // Create model when level changes
  useEffect(() => {
    connection.startLeanClient().then((leanClient) => {
      if (editor) {

        const uri = monaco.Uri.parse(`file:///${worldId}/${levelId}`)
        const model = monaco.editor.getModel(uri) ??
          monaco.editor.createModel('', 'lean4', uri)

        editor.setModel(model)
        infoviewApi.serverRestarted(leanClient.initializeResult)
        infoProvider.openPreview(editor, infoviewApi)
        new LeanTaskGutter(infoProvider.client, editor)

        new AbbreviationRewriter(new AbbreviationProvider(), model, editor)
      }
    })

  }, [editor, levelId, connection])

  return {editor, infoProvider}
}
