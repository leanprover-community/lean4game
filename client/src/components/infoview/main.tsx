/* Partly copied from https://github.com/leanprover/vscode-lean4/blob/master/lean4-infoview/src/infoview/main.tsx */

import * as React from 'react';
import type { DidCloseTextDocumentParams, DocumentUri } from 'vscode-languageserver-protocol';

import 'tachyons/css/tachyons.css';
import '@vscode/codicons/dist/codicon.css';
import '../../../../node_modules/vscode-lean4/lean4-infoview/src/infoview/index.css';
import '../../css/infoview.css'
import "../../css/tab_bar.css"

import { LeanFileProgressParams, LeanFileProgressProcessingInfo, defaultInfoviewConfig } from '@leanprover/infoview-api';
import { useClientNotificationEffect, useEventResult, useServerNotificationEffect, useServerNotificationState } from '../../../../node_modules/vscode-lean4/lean4-infoview/src/infoview/util';
import { EditorContext, ConfigContext, ProgressContext, VersionContext } from '../../../../node_modules/vscode-lean4/lean4-infoview/src/infoview/contexts';
import { RpcContext, WithRpcSessions, useRpcSessionAtPos } from '../../../../node_modules/vscode-lean4/lean4-infoview/src/infoview/rpcSessions';
import { ServerVersion } from '../../../../node_modules/vscode-lean4/lean4-infoview/src/infoview/serverVersion';

import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faDeleteLeft, faHome, faArrowRight } from '@fortawesome/free-solid-svg-icons'
import * as monaco from 'monaco-editor/esm/vs/editor/editor.api.js'

import { Markdown } from '../markdown';

import { Infos } from './infos';
import { Errors, WithLspDiagnosticsContext } from './messages';
import { Goal, isLastStepWithErrors, lastStepHasErrors, loadGoals } from './goals';
import { MonacoEditorContext } from './context';
import { Typewriter, getInteractiveDiagsAt, hasInteractiveErrors } from './typewriter';
import { Button } from '../button';
import { CircularProgress } from '@mui/material';
import { GameHint, InteractiveGoalsWithHints, ProofState } from './rpc_api';
import { Hint, Hints, MoreHelpButton, filterHints } from '../hints';
import { DocumentPosition } from '../../../../node_modules/vscode-lean4/lean4-infoview/src/infoview/util';
import { DiagnosticSeverity } from 'vscode-languageclient';
import { useTranslation } from 'react-i18next';
import path from 'path';
import { useGameTranslation } from '../../utils/translation';
import { useAtom } from 'jotai';
import { gameIdAtom, levelIdAtom, worldIdAtom } from '../../store/location-atoms';
import { completedAtom } from '../../store/progress-atoms';
import { gameInfoAtom, levelInfoAtom } from '../../store/query-atoms';
import { crashedAtom, interimDiagsAtom, lockEditorModeAtom, proofAtom, typewriterContentAtom, typewriterModeAtom } from '../../store/editor-atoms';
import { inventoryAtom } from '../../store/inventory-atoms';
import { mobileAtom } from '../../store/preferences-atoms';
import { deletedChatAtom, helpAtom, selectedStepAtom } from '../../store/chat-atoms';

/** Wrapper for the two editors. It is important that the `div` with `codeViewRef` is
 * always present, or the monaco editor cannot start.
 */
export function DualEditor({ codeviewRef } : { codeviewRef: any }) {
  const [typewriterMode] = useAtom(typewriterModeAtom)
  const ec = React.useContext(EditorContext)
  const showTypewriter = Boolean(ec) && typewriterMode
  return <>
    <div className={showTypewriter ? 'hidden' : ''}>
      <ExerciseStatement showLeanStatement={true} />
      <div ref={codeviewRef} className={'codeview'}></div>
    </div>
    {ec ?
      <DualEditorMain /> :
      // TODO: Style this if relevant.
      <></>
    }
  </>
}

/** The part of the two editors that needs the editor connection first */
function DualEditorMain() {
  const ec = React.useContext(EditorContext)
  const [gameId] = useAtom(gameIdAtom)
  const [worldId] = useAtom(worldIdAtom)
  const [levelId] = useAtom(levelIdAtom)
  const [{ data: gameInfo }] = useAtom(gameInfoAtom)
  const [{ data: levelInfo }] = useAtom(levelInfoAtom)

  const [, setCompleted] = useAtom(completedAtom)

  const [, addToInventory] = useAtom(inventoryAtom)
  const [typewriterMode, setTypewriterMode] = useAtom(typewriterModeAtom)

  const [proof] = useAtom(proofAtom)

  React.useEffect(() => {
    if (proof?.completed) {
      setCompleted(true)

      // On completion, add the names of all new items to the local storage
      let newTiles = [
        ...levelInfo?.tactics ?? [],
        ...levelInfo?.lemmas ?? [],
        ...levelInfo?.definitions ?? []
      ].filter((tile) => tile.new).map((tile) => tile.name)

      // Add the proven statement to the local storage as well.
      if (levelInfo?.statementName != null) {
        newTiles.push(levelInfo?.statementName)
      }
      addToInventory(newTiles)
    }
  }, [proof, levelInfo])

  /* Set up updates to the global infoview state on editor events. */
  const config = useEventResult(ec.events.changedInfoviewConfig) ?? defaultInfoviewConfig;

  const [allProgress, _1] = useServerNotificationState(
    '$/lean/fileProgress',
    new Map<DocumentUri, LeanFileProgressProcessingInfo[]>(),
    async (params: LeanFileProgressParams) => (allProgress) => {
      const newProgress = new Map(allProgress);
      return newProgress.set(params.textDocument.uri, params.processing);
    }, [])
  const serverVersion = useEventResult(ec.events.serverRestarted, result => new ServerVersion(result.serverInfo?.version ?? ''))

  return <>
    <ConfigContext.Provider value={config}>
      <VersionContext.Provider value={serverVersion}>
        <WithRpcSessions>
          <WithLspDiagnosticsContext>
            <ProgressContext.Provider value={allProgress}>
              {(typewriterMode) ?
                <TypewriterInterfaceWrapper/>
                :
                <Main key={`${worldId}/${levelId}`} />
              }
            </ProgressContext.Provider>
          </WithLspDiagnosticsContext>
        </WithRpcSessions>
      </VersionContext.Provider>
    </ConfigContext.Provider>
  </>
}

/** The mathematical formulation of the statement, supporting e.g. Latex
 * It takes three forms, depending on the precence of name and description:
 * - Theorem xyz: description
 * - Theorem xyz
 * - Exercises: description
 *
 * If `showLeanStatement` is true, it will additionally display the lean code.
 */
function ExerciseStatement({ showLeanStatement = false }) {
  const { t : gT } = useGameTranslation()
  const { t } = useTranslation()
  const [gameId] = useAtom(gameIdAtom)
  const [{ data: levelInfo }] = useAtom(levelInfoAtom)

  if (!(levelInfo?.descrText || levelInfo?.descrFormat)) { return <></> }
  return <>
    <div className="exercise-statement">
      {levelInfo?.descrText ?
        <Markdown>
          {(levelInfo?.displayName ? `**${t("Theorem")}** \`${levelInfo?.displayName}\`: ` : '') + t(levelInfo?.descrText, {ns: gameId})}
        </Markdown> : levelInfo?.displayName &&
        <Markdown>
          {(levelInfo?.displayName ? `**${t("Theorem")}** \`${levelInfo?.displayName}\`: ` : '') + gT(levelInfo?.descrText ?? "")}
        </Markdown>
      }
      {levelInfo?.descrFormat && showLeanStatement &&
        <p><code className="lean-code">{levelInfo?.descrFormat}</code></p>
      }
    </div>
  </>
}

// TODO: This is only used in `EditorInterface`
// while `TypewriterInterface` has this copy-pasted in.
export function Main() {
  let { t } = useTranslation()
  const { t: gT } = useGameTranslation()
  const [lockEditorMode] = useAtom(lockEditorModeAtom)
  const ec = React.useContext(EditorContext);
  const [gameId] = useAtom(gameIdAtom)
  const [worldId] = useAtom(worldIdAtom)
  const [levelId] = useAtom(levelIdAtom)
  const [{ data: gameInfo }] = useAtom(gameInfoAtom)
  const [{ data: levelInfo }] = useAtom(levelInfoAtom)
  const [help, setHelp] = useAtom(helpAtom)

  const [typewriterMode] = useAtom(typewriterModeAtom)

  const [proof, setProof] = useAtom(proofAtom)
  const [, setCrashed] = useAtom(crashedAtom)
  const [selectedStep, setSelectedStep] = useAtom(selectedStepAtom)
  const editor = React.useContext(MonacoEditorContext)
  const model = editor?.getModel()
  const uri = model?.uri.toString()
  const rpcSess = useRpcSessionAtPos({ uri: uri ?? '', line: 0, character: 0 })

  React.useEffect(() => {
    if (!uri || !worldId || !levelId) {
      return
    }
    loadGoals(rpcSess, uri, worldId, levelId, setProof, setCrashed)
  }, [rpcSess, uri, worldId, levelId, setProof, setCrashed])

  function toggleSelection(line: number) {
    return (ev: any) => {
      console.debug('toggled selection')
      if (selectedStep == line) {
        setSelectedStep(null)
      } else {
        setSelectedStep(line)
      }
    }
  }
  //console.debug(`template: ${props.data?.template}`)

  // React.useEffect (() => {
  //   if (props.data.template) {
  //     let code: string = selectCode(gameId, worldId, levelId)(store.getState())
  //     if (!code.length) {
  //       //models.push(monaco.editor.createModel(code, 'lean4', uri))
  //     }
  //   }
  // }, [props.data.template])

  /* Set up updates to the global infoview state on editor events. */
  const config = useEventResult(ec.events.changedInfoviewConfig) ?? defaultInfoviewConfig;

  const [allProgress, _1] = useServerNotificationState(
    '$/lean/fileProgress',
    new Map<DocumentUri, LeanFileProgressProcessingInfo[]>(),
    async (params: LeanFileProgressParams) => (allProgress) => {
      const newProgress = new Map(allProgress);
      return newProgress.set(params.textDocument.uri, params.processing);
    },
    []
  );

  const curUri = useEventResult(ec.events.changedCursorLocation, loc => loc?.uri);

  const curPos: DocumentPosition | undefined =
    useEventResult(ec.events.changedCursorLocation, loc => loc ? { uri: loc.uri, ...loc.range.start } : undefined)

  React.useEffect(() => {
    if (typewriterMode) {
      return
    }
    if (!uri) {
      return
    }
    loadGoals(rpcSess, uri, worldId!, levelId!, setProof, setCrashed)
  }, [typewriterMode, lockEditorMode, uri, worldId, levelId, rpcSess, setProof, setCrashed])

  useServerNotificationEffect('textDocument/publishDiagnostics', (params: any) => {
    if (typewriterMode) {
      return
    }
    if (!uri || params?.uri !== uri) {
      return
    }
    loadGoals(rpcSess, uri, worldId!, levelId!, setProof, setCrashed)
  }, [typewriterMode, lockEditorMode, uri, worldId, levelId, rpcSess, setProof, setCrashed])

  const hintLine = (() => {
    const isEditorMode = !(typewriterMode)
    const curLine = Number.isFinite(curPos?.line)
      ? curPos.line
      : (Number.isFinite((curPos as any)?._line) ? (curPos as any)._line : undefined)
    const curChar = Number.isFinite(curPos?.character)
      ? curPos.character
      : (Number.isFinite((curPos as any)?._character) ? (curPos as any)._character : undefined)
    if (isEditorMode && Number.isFinite(curLine)) {
      const baseLine = curLine
      return (curChar === 0 && baseLine > 0) ? baseLine - 1 : baseLine
    }
    if (Number.isFinite(selectedStep)) {
      return selectedStep
    }
    if (!proof?.steps?.length) {
      return 0
    }
    const lastIndex = proof.steps.length - 1
    return lastStepHasErrors(proof) ? Math.max(0, lastIndex - 1) : lastIndex
  })()

  const clampedHintLine = Math.max(0, Math.min(Number.isFinite(hintLine) ? hintLine : 0, (proof?.steps?.length ?? 1) - 1))
  const hintStepIndex = (() => {
    if (Number.isFinite(selectedStep)) {
      return selectedStep
    }
    if (!proof?.steps?.length) {
      return 0
    }
    const maxIndex = proof.steps.length - 1
    return Math.min(clampedHintLine + 1, maxIndex)
  })()
  const hintsToShow = (() => {
    if (!proof?.steps?.length) {
      return undefined
    }
    return proof.steps[hintStepIndex]?.goals?.[0]?.hints
  })()

  // Effect when the cursor changes in the editor
  React.useEffect(() => {
    // TODO: this is a bit of a hack and will yield unexpected behaviour if lines
    // are indented.
    const newPos = curPos?.line + (curPos?.character == 0 ? 0 : 1)

    if (Number.isFinite(newPos)) {
      // scroll the chat along
      setSelectedStep(newPos)
    }
  }, [curPos])

  useClientNotificationEffect(
    'textDocument/didClose',
    (params: DidCloseTextDocumentParams) => {
      if (ec.events.changedCursorLocation.current &&
        ec.events.changedCursorLocation.current.uri === params.textDocument.uri) {
        ec.events.changedCursorLocation.fire(undefined)
      }
    },
    []
  );

  const serverVersion =
    useEventResult(ec.events.serverRestarted, result => new ServerVersion(result.serverInfo?.version ?? ''))
  const serverStoppedResult = useEventResult(ec.events.serverStopped);
  // NB: the cursor may temporarily become `undefined` when a file is closed. In this case
  // it's important not to reconstruct the `WithBlah` wrappers below since they contain state
  // that we want to persist.
  let ret
  if (serverStoppedResult) {
    ret = <div><p>{serverStoppedResult.message}</p><p className="error">{serverStoppedResult.reason}</p></div>
  } else {
    ret = <div className="infoview vscode-light">
      {proof?.completedWithWarnings &&
        <div className="level-completed">
          {proof?.completed ? t("Level completed! 🎉") : t("Level completed with warnings 🎭")}
        </div>
      }
      <Infos />
      {hintsToShow && (
        <Hints hints={hintsToShow}
          showHidden={help.has(hintStepIndex)} step={hintStepIndex}
          selected={selectedStep} toggleSelection={toggleSelection(hintStepIndex)}
          lastLevel={hintStepIndex == proof?.steps.length - 1}/>
      )}
      <MoreHelpButton selected={curPos?.line}/>
    </div>
  }

  return ret
}

const goalFilter = {
  reverse: false,
  showType: true,
  showInstance: true,
  showHiddenAssumption: true,
  showLetValue: true
}

/** The display of a single entered lean command */
function Command({ proof, i, deleteProof }: { proof: ProofState, i: number, deleteProof: any }) {
  let {t} = useTranslation()

  // The first step will always have an empty command
  if (!proof?.steps[i]?.command) { return <></> }

  if (isLastStepWithErrors(proof, i)) {
    // If the last step has errors, we display the command in a different style
    // indicating that it will be removed on the next try.
    return <div className="failed-command">
      <i>{t("Failed command")}</i>: {proof?.steps[i].command}
    </div>
  } else {
    return <div className="command">
      <div className="command-text">{proof?.steps[i].command}</div>
      <Button  className="undo-button btn btn-inverted" title={t("Retry proof from here")} onClick={deleteProof}>
        <FontAwesomeIcon icon={faDeleteLeft} />&nbsp;{t("Retry")}
      </Button>
    </div>
  }
}

/** The tabs of goals that lean ahs after the command of this step has been processed */
function GoalsTabs({ proofStep, last, onClick, onGoalChange=(n)=>{}}: { proofStep: InteractiveGoalsWithHints, last : boolean, onClick? : any, onGoalChange?: (n?: number) => void }) {
  let { t } = useTranslation()
  const [mobile] = useAtom(mobileAtom)
  const [selectedGoal, setSelectedGoal] = React.useState<number>(0)

  if (proofStep.goals.length == 0) {
    return <></>
  }

  return <div className="goal-tabs" onClick={onClick}>
    <div className={`tab-bar ${last ? 'current' : ''}`}>
      {proofStep.goals.map((goal, i) => (
        // TODO: Should not use index as key.
        <div key={`proof-goal-${i}`} className={`tab ${i == (selectedGoal) ? "active" : ""}`} onClick={(ev) => { onGoalChange(i); setSelectedGoal(i); ev.stopPropagation() }}>
          {i ? t("Goal") + ` ${i + 1}` : t("Active Goal")}
        </div>
      ))}
    </div>
    <div className="goal-tab vscode-light" style={{flexDirection: mobile ? "column" : "row"}}>
      <Goal typewriter={false} filter={goalFilter} goal={proofStep.goals[selectedGoal]?.goal} />
    </div>
  </div>
}

// Splitting up Typewriter into two parts is a HACK
export function TypewriterInterfaceWrapper() {
  const ec = React.useContext(EditorContext)

  useClientNotificationEffect(
    'textDocument/didClose',
    (params: DidCloseTextDocumentParams) => {
      if (ec.events.changedCursorLocation.current &&
        ec.events.changedCursorLocation.current.uri === params.textDocument.uri) {
        ec.events.changedCursorLocation.fire(undefined)
      }
    }, []
  )

  const serverVersion =
    useEventResult(ec.events.serverRestarted, result => new ServerVersion(result.serverInfo?.version ?? ''))
  const serverStoppedResult = useEventResult(ec.events.serverStopped);
  // NB: the cursor may temporarily become `undefined` when a file is closed. In this case
  // it's important not to reconstruct the `WithBlah` wrappers below since they contain state
  // that we want to persist.

  if (serverStoppedResult) {
    return <div>
      <p>{serverStoppedResult.message}</p>
      <p className="error">{serverStoppedResult.reason}</p>
    </div>
  }

  return <TypewriterInterface />
}

/** The interface in command line mode */
export function TypewriterInterface() {
  let { t } = useTranslation()
  const ec = React.useContext(EditorContext)
  const [gameId, navigateToGame] = useAtom(gameIdAtom)
  const [worldId] = useAtom(worldIdAtom)
  const [levelId, navigateToLevel] = useAtom(levelIdAtom)
  const [{ data: gameInfo }] = useAtom(gameInfoAtom)
  const [help, setHelp] = useAtom(helpAtom)

  const editor = React.useContext(MonacoEditorContext)
  const model = editor?.getModel()
  const uri = model?.uri.toString() ?? ''

  const worldSize = gameInfo?.worldSize?.[worldId ?? ""] ?? 0

  const fallbackUri = `file:///${worldId}/${levelId}.lean`
  const effectiveUri = uri || fallbackUri
  let image: string | undefined = gameInfo?.worlds?.nodes[worldId!]?.image


  const [disableInput, setDisableInput] = React.useState<boolean>(false)
  const [loadingProgress, setLoadingProgress] = React.useState<number>(0)
  const [, setDeletedChat] = useAtom(deletedChatAtom)
  const [mobile] = useAtom(mobileAtom)
  const [proof, setProof ] = useAtom(proofAtom)
  const [crashed, setCrashed ] = useAtom(crashedAtom)
  const [interimDiags ] = useAtom(interimDiagsAtom)

  const [, setTypewriter] = useAtom(typewriterContentAtom)
  const [selectedStep, setSelectedStep] = useAtom(selectedStepAtom)

  const proofPanelRef = React.useRef<HTMLDivElement>(null)
  // const config = useEventResult(ec.events.changedInfoviewConfig) ?? defaultInfoviewConfig;
  // const curUri = useEventResult(ec.events.changedCursorLocation, loc => loc?.uri);

  const rpcSess = useRpcSessionAtPos({uri: effectiveUri, line: 0, character: 0})

  React.useEffect(() => {
    if (!effectiveUri) {
      return
    }
    setCrashed(false)
    loadGoals(rpcSess, effectiveUri, worldId!, levelId!, setProof, setCrashed)
  }, [rpcSess, effectiveUri, worldId, levelId, setProof, setCrashed])

  /** Delete all proof lines starting from a given line.
  * Note that the first line (i.e. deleting everything) is `1`!
  */
  function deleteProof(line: number) {
    return (ev) => {
      let deletedChat: Array<GameHint> = []
      proof?.steps.slice(line).map((step, i) => {
        let filteredHints = filterHints(step.goals[0]?.hints, proof?.steps[i-1]?.goals[0]?.hints)

        // Only add these hidden hints to the deletion stack which were visible
        deletedChat = [...deletedChat, ...filteredHints.filter(hint => (!hint.hidden || help.has(line + i)))]
      })
      setDeletedChat(deletedChat)

      // delete showHelp for deleted steps
      setHelp(new Set(Array.from(help).filter(i => i < line - 1)))

      editor.executeEdits("typewriter", [{
        range: monaco.Selection.fromPositions(
          { lineNumber: line, column: 1 },
          editor.getModel()?.getFullModelRange().getEndPosition()
        ),
        text: '',
        forceMoveMarkers: false
      }])
      setSelectedStep(null)
      setTypewriter(proof?.steps[line].command)
      // Reload proof on deleting
      loadGoals(rpcSess, uri, worldId!, levelId!, setProof, setCrashed)
      ev.stopPropagation()
    }
  }

  function toggleSelectStep(line: number) {
    return (ev) => {
      if (mobile) {return}
      if (selectedStep == line) {
        setSelectedStep(null)
        console.debug(`unselected step`)
      } else {
        setSelectedStep(line)
        console.debug(`step ${line} selected`)
      }
    }
  }

   // Scroll to the end of the proof if it is updated.
   React.useEffect(() => {
    if (proof?.steps.length > 1) {
      proofPanelRef.current?.lastElementChild?.scrollIntoView() //scrollTo(0,0)
    } else {
      proofPanelRef.current?.scrollTo(0,0)
    }
    // also reenable the commandline when the proof changes

    // BUG: If selecting 2nd goal on a intermediate proofstep and then delete proof to there,
    // the commandline is not displaying disabled even though it should.
    setDisableInput(false)
  }, [proof])

  // Scroll to element if selection changes
  React.useEffect(() => {
    if (typeof selectedStep !== 'undefined') {
      Array.from(proofPanelRef.current?.getElementsByClassName(`step-${selectedStep}`)).map((elem) => {
        elem.scrollIntoView({ block: "center" })
      })
    }
  }, [selectedStep])

  // TODO: superfluous, can be replaced with `withErr` from above
  let lastStepErrors = proof?.steps.length ? hasInteractiveErrors(getInteractiveDiagsAt(proof, proof?.steps.length)) : false


  useServerNotificationEffect("$/game/loading", (params : any) => {
    if (params.kind == "loadConstants") {
      setLoadingProgress(params.counter/100*50)
    } else if (params.kind == "finalizeExtensions") {
      setLoadingProgress(50 + params.counter/150*50)
    } else {
      console.error(`Unknown loading kind: ${params.kind}`)
    }
  })

  let introText: Array<string> = t(gameInfo?.introduction ?? "", {ns: gameId}).split(/\n(\s*\n)+/)

  return <div className="typewriter-interface">
    <RpcContext.Provider value={rpcSess}>
    <div className="content">
      <div className='world-image-container empty'>
        {image &&
          <img className="contain" src={path.join("data", gameId!, image)} alt="" />
        }

      </div>
      <div className="tmp-pusher">
        {/* <div className="world-image-container empty">

        </div> */}
      </div>
      <div className='proof' ref={proofPanelRef}>
        <ExerciseStatement showLeanStatement={true} />
        {((crashed && (interimDiags.length > 0 || proof?.steps.length > 0))) ? <div>
          <p className="crashed_message">{t("Crashed! Go to editor mode and fix your proof! Last server response:")}</p>
          {interimDiags.map((diag, index) => {
            const severityClass = diag.severity ? {
              [DiagnosticSeverity.Error]: 'error',
              [DiagnosticSeverity.Warning]: 'warning',
              [DiagnosticSeverity.Information]: 'information',
              [DiagnosticSeverity.Hint]: 'hint',
            }[diag.severity] : '';

            return <div key={`interim-diag-${index}`}>
              <div className={`${severityClass} ml1 message`}>
                <p className="mv2">{t("Line")}&nbsp;{diag.range.start.line}, {t("Character")}&nbsp;{diag.range.start.character}</p>
                <pre className="font-code pre-wrap">
                  {diag.message}
                </pre>
                </div>
            </div>
          })}

        </div> : proof?.steps.length ?
          <>
            {proof?.steps.map((step, i) => {
              let filteredHints = filterHints(step.goals[0]?.hints, proof?.steps[i-1]?.goals[0]?.hints)

              // if (i == proof?.steps.length - 1 && hasInteractiveErrors(step.diags)) {
              //   // if the last command contains an error, we only display the errors but not the
              //   // entered command as it is still present in the command line.
              //   // TODO: Should not use index as key.
              //   return <div key={`proof-step-${i}`} className={`step step-${i}`}>
              //     <Errors errors={step.diags} typewriterMode={true} />
              //   </div>
              // } else {
                return <div key={`proof-step-${i}`} className={`step step-${i}` + (selectedStep == i ? ' selected' : '')}>
                  <Command proof={proof} i={i} deleteProof={deleteProof(i)} />
                  <Errors errors={step.diags} typewriterMode={true} />
                  {mobile && i == 0 && gameInfo?.introduction &&
                    introText?.filter(it => it.trim()).map(((it, i) =>
                      // Show the level's intro text as hints, too
                      <Hint key={`intro-p-${i}`}
                        hint={{text: it, hidden: false, rawText: it, varNames: []}} step={0} selected={selectedStep} toggleSelection={toggleSelectStep(0)} />
                    ))
                  }
                  {mobile &&
                    <Hints key={`hints-${i}`}
                      hints={filteredHints} showHidden={help.has(i)} step={i}
                      selected={selectedStep} toggleSelection={toggleSelectStep(i)}/>
                  }
                  {/* <GoalsTabs proofStep={step} last={i == proof?.steps.length - (lastStepErrors ? 2 : 1)} onClick={toggleSelectStep(i)} onGoalChange={i == proof?.steps.length - 1 - withErr ? (n) => setDisableInput(n > 0) : (n) => {}}/> */}
                  {!(isLastStepWithErrors(proof, i)) &&
                    <GoalsTabs proofStep={step} last={i == proof?.steps.length - (lastStepHasErrors(proof) ? 2 : 1)} onClick={toggleSelectStep(i)} onGoalChange={i == proof?.steps.length - (lastStepHasErrors(proof) ? 2 : 1) ? (n) => setDisableInput(n > 0) : (n) => {}}/>
                  }
                  {mobile && i == proof?.steps.length - 1 &&
                    <MoreHelpButton selected={null} />
                  }

                  {/* Show a message that there are no goals left */}
                  {/* {!step.goals.length && (
                    <div className="message information">
                      {proof?.completed ?
                        <p>Level completed! 🎉</p> :
                        <p>
                          <b>no goals left</b><br />
                          <i>This probably means you solved the level with warnings or Lean encountered a parsing error.</i>
                        </p>
                      }
                    </div>
                  )} */}
                </div>
              }
            //}
            )}
            {proof?.diagnostics.length > 0 &&
              <div key={`proof-step-remaining`} className="step step-remaining">
                <Errors errors={proof?.diagnostics} typewriterMode={true} />
              </div>
            }
            {mobile && proof?.completed &&
              <div className="button-row mobile">
                {levelId! >= worldSize ?
                  <Button onClick={() => navigateToGame(gameId!)} >
                    <FontAwesomeIcon icon={faHome} />&nbsp;{t("Home")}
                  </Button>
                :
                  <Button onClick={() => navigateToLevel(levelId! + 1)} >
                    Next&nbsp;<FontAwesomeIcon icon={faArrowRight} />
                  </Button>
                }
              </div>
            }
          </> :
          <CircularProgress />
          // <CircularProgress variant="determinate" value={100*(1 - 1.024 ** (- Math.max(loadingProgress, 1)))} />
        // note: since we don't know the total number of files,
        // we use a function which strictly monotonely increases towards `100` as `x → ∞`
        // The base is chosen at random s.t. we get roughly 91% for `x = 100`.
        }
      </div>
    </div>
    <Typewriter disabled={disableInput || crashed}/>
    </RpcContext.Provider>
  </div>
}
