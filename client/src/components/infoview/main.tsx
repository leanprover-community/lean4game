/* Partly copied from https://github.com/leanprover/vscode-lean4/blob/master/lean4-infoview/src/infoview/main.tsx */

import * as React from 'react';
import type { DidCloseTextDocumentParams, DidChangeTextDocumentParams, Location, DocumentUri } from 'vscode-languageserver-protocol';

import 'tachyons/css/tachyons.css';
import '@vscode/codicons/dist/codicon.css';
import '../../../../node_modules/lean4-infoview/src/infoview/index.css';
import '../../css/infoview.css'

import { LeanFileProgressParams, LeanFileProgressProcessingInfo, defaultInfoviewConfig, EditorApi, InfoviewApi } from '@leanprover/infoview-api';
import { useClientNotificationEffect, useServerNotificationEffect, useEventResult, useServerNotificationState } from '../../../../node_modules/lean4-infoview/src/infoview/util';
import { EditorContext, ConfigContext, ProgressContext, VersionContext } from '../../../../node_modules/lean4-infoview/src/infoview/contexts';
import { RpcContext, WithRpcSessions, useRpcSessionAtPos } from '../../../../node_modules/lean4-infoview/src/infoview/rpcSessions';
import { ServerVersion } from '../../../../node_modules/lean4-infoview/src/infoview/serverVersion';

import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faDeleteLeft, faHome, faArrowRight, faArrowLeft, faRotateLeft } from '@fortawesome/free-solid-svg-icons'
import * as monaco from 'monaco-editor/esm/vs/editor/editor.api.js'

import { GameIdContext } from '../../app';
import { useAppDispatch, useAppSelector } from '../../hooks';
import { LevelInfo, useGetGameInfoQuery } from '../../state/api';
import { changedInventory, levelCompleted, selectCode, selectCompleted, selectInventory } from '../../state/progress';
import Markdown from '../markdown';

import { Infos } from './infos';
import { AllMessages, Errors, WithLspDiagnosticsContext } from './messages';
import { Goal, isLastStepWithErrors, lastStepHasErrors, loadGoals } from './goals';
import { DeletedChatContext, InputModeContext, PreferencesContext, MonacoEditorContext, ProofContext, SelectionContext, WorldLevelIdContext } from './context';
import { Typewriter, getInteractiveDiagsAt, hasErrors, hasInteractiveErrors } from './typewriter';
import { InteractiveDiagnostic } from '@leanprover/infoview/*';
import { Button } from '../button';
import { CircularProgress } from '@mui/material';
import { GameHint, InteractiveGoalsWithHints, ProofState } from './rpc_api';
import { store } from '../../state/store';
import { Hints, MoreHelpButton, filterHints } from '../hints';
import { DocumentPosition } from '../../../../node_modules/lean4-infoview/src/infoview/util';
import { DiagnosticSeverity } from 'vscode-languageclient';
import { useTranslation } from 'react-i18next';
import path from 'path';


/** Wrapper for the two editors. It is important that the `div` with `codeViewRef` is
 * always present, or the monaco editor cannot start.
 */
export function DualEditor({ level, codeviewRef, levelId, worldId, worldSize }) {
  const ec = React.useContext(EditorContext)
  const { typewriterMode, lockEditorMode } = React.useContext(InputModeContext)
  return <>
    <div className={(typewriterMode && !lockEditorMode) ? 'hidden' : ''}>
      <ExerciseStatement data={level} showLeanStatement={true} />
      <div ref={codeviewRef} className={'codeview'}></div>
    </div>
    {ec ?
      <DualEditorMain worldId={worldId} levelId={levelId} level={level} worldSize={worldSize} /> :
      // TODO: Style this if relevant.
      <></>
    }
  </>
}

/** The part of the two editors that needs the editor connection first */
function DualEditorMain({ worldId, levelId, level, worldSize }: { worldId: string, levelId: number, level: LevelInfo, worldSize: number }) {
  const ec = React.useContext(EditorContext)
  const gameId = React.useContext(GameIdContext)
  const { typewriterMode, lockEditorMode } = React.useContext(InputModeContext)

  const {proof, setProof} = React.useContext(ProofContext)

  const dispatch = useAppDispatch()

  React.useEffect(() => {
    if (proof?.completed) {
      dispatch(levelCompleted({ game: gameId, world: worldId, level: levelId }))

      // On completion, add the names of all new items to the local storage
      let newTiles = [
        ...level?.tactics,
        ...level?.lemmas,
        ...level?.definitions
      ].filter((tile) => tile.new).map((tile) => tile.name)

      // Add the proven statement to the local storage as well.
      if (level?.statementName != null) {
        newTiles.push(level?.statementName)
      }

      let inv: string[] = selectInventory(gameId)(store.getState())

      // add new items and remove duplicates
      let newInv = [...inv, ...newTiles].filter((item, i, array) => array.indexOf(item) == i)

      dispatch(changedInventory({ game: gameId, inventory: newInv }))

    }
  }, [proof, level])

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
              {(typewriterMode && !lockEditorMode) ?
                <TypewriterInterfaceWrapper world={worldId} level={levelId} data={level} worldSize={worldSize}/>
                :
                <Main key={`${worldId}/${levelId}`} world={worldId} level={levelId} data={level} />
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
function ExerciseStatement({ data, showLeanStatement = false }) {
  let { t } = useTranslation()
  const gameId = React.useContext(GameIdContext)

  if (!(data?.descrText || data?.descrFormat)) { return <></> }
  return <>
    <div className="exercise-statement">
      {data?.descrText &&
        <Markdown>
          {(data?.displayName ? `**Theorem** \`${data?.displayName}\`: ` : '') + t(data?.descrText, {ns: gameId})}
        </Markdown>
      }
      {data?.descrFormat && showLeanStatement &&
        <p><code className="lean-code">{data?.descrFormat}</code></p>
      }
    </div>
  </>
}

// TODO: This is only used in `EditorInterface`
// while `TypewriterInterface` has this copy-pasted in.
export function Main(props: { world: string, level: number, data: LevelInfo}) {
  let { t } = useTranslation()
  const ec = React.useContext(EditorContext);
  const gameId = React.useContext(GameIdContext)
  const {worldId, levelId} = React.useContext(WorldLevelIdContext)

  const { proof, setProof } = React.useContext(ProofContext)
  const {selectedStep, setSelectedStep} = React.useContext(SelectionContext)
  const { setDeletedChat, showHelp, setShowHelp } = React.useContext(DeletedChatContext)


  function toggleSelection(line: number) {
    return (ev) => {
      console.debug('toggled selection')
      if (selectedStep == line) {
        setSelectedStep(undefined)
      } else {
        setSelectedStep(line)
      }
    }
  }
  console.debug(`template: ${props.data?.template}`)

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

  // Effect when the cursor changes in the editor
  React.useEffect(() => {
    // TODO: this is a bit of a hack and will yield unexpected behaviour if lines
    // are indented.
    let newPos = curPos?.line + (curPos?.character == 0 ? 0 : 1)

    // scroll the chat along
    setSelectedStep(newPos)
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
  if (!serverVersion) {
    ret = <p>{t("Waiting for Lean server to start…")}</p>
  } else if (serverStoppedResult) {
    ret = <div><p>{serverStoppedResult.message}</p><p className="error">{serverStoppedResult.reason}</p></div>
  } else {
    ret = <div className="infoview vscode-light">
      {proof?.completedWithWarnings &&
        <div className="level-completed">
          {proof?.completed ? t("Level completed! 🎉") : t("Level completed with warnings 🎭")}
        </div>
      }
      <Infos />
      <Hints hints={proof?.steps[curPos?.line]?.goals[0]?.hints}
        showHidden={showHelp.has(curPos?.line)} step={curPos?.line}
        selected={selectedStep} toggleSelection={toggleSelection(curPos?.line)}
        lastLevel={curPos?.line == proof?.steps.length - 1}/>
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
      <Button to="" className="undo-button btn btn-inverted" title={t("Retry proof from here")} onClick={deleteProof}>
        <FontAwesomeIcon icon={faDeleteLeft} />&nbsp;{t("Retry")}
      </Button>
    </div>
  }
}

// const MessageView = React.memo(({uri, diag}: MessageViewProps) => {
//   const ec = React.useContext(EditorContext);
//   const fname = escapeHtml(basename(uri));
//   const {line, character} = diag.range.start;
//   const loc: Location = { uri, range: diag.range };
//   const text = TaggedText_stripTags(diag.message);
//   const severityClass = diag.severity ? {
//       [DiagnosticSeverity.Error]: 'error',
//       [DiagnosticSeverity.Warning]: 'warning',
//       [DiagnosticSeverity.Information]: 'information',
//       [DiagnosticSeverity.Hint]: 'hint',
//   }[diag.severity] : '';
//   const title = `Line ${line+1}, Character ${character}`;

//   // Hide "unsolved goals" messages
//   let message;
//   if ("append" in diag.message && "text" in diag.message.append[0] &&
//     diag.message?.append[0].text === "unsolved goals") {
//       message = diag.message.append[0]
//   } else {
//       message = diag.message
//   }

//   const { typewriterMode } = React.useContext(InputModeContext)

//   return (
//   // <details open>
//       // <summary className={severityClass + ' mv2 pointer'}>{title}
//       //     <span className="fr">
//       //         <a className="link pointer mh2 dim codicon codicon-go-to-file"
//       //            onClick={e => { e.preventDefault(); void ec.revealLocation(loc); }}
//       //            title="reveal file location"></a>
//       //         <a className="link pointer mh2 dim codicon codicon-quote"
//       //            data-id="copy-to-comment"
//       //            onClick={e => {e.preventDefault(); void ec.copyToComment(text)}}
//       //            title="copy message to comment"></a>
//       //         <a className="link pointer mh2 dim codicon codicon-clippy"
//       //            onClick={e => {e.preventDefault(); void ec.api.copyToClipboard(text)}}
//       //            title="copy message to clipboard"></a>
//       //     </span>
//       // </summary>
//       <div className={severityClass + ' ml1 message'}>
//           {!typewriterMode && <p className="mv2">{title}</p>}
//           <pre className="font-code pre-wrap">
//               <InteractiveMessage fmt={message} />
//           </pre>
//       </div>
//   // </details>
//   )
// }, fastIsEqual)

/** The tabs of goals that lean ahs after the command of this step has been processed */
function GoalsTabs({ proofStep, last, onClick, onGoalChange=(n)=>{}}: { proofStep: InteractiveGoalsWithHints, last : boolean, onClick? : any, onGoalChange?: (n?: number) => void }) {
  let { t } = useTranslation()
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
    <div className="goal-tab vscode-light">
      <Goal typewriter={false} filter={goalFilter} goal={proofStep.goals[selectedGoal]?.goal} />
    </div>
  </div>
}

// Splitting up Typewriter into two parts is a HACK
export function TypewriterInterfaceWrapper(props: { world: string, level: number, data: LevelInfo, worldSize: number }) {
  const ec = React.useContext(EditorContext)
  const gameId = React.useContext(GameIdContext)

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

  if (!serverVersion) { return <></> }
  if (serverStoppedResult) {
    return <div>
      <p>{serverStoppedResult.message}</p>
      <p className="error">{serverStoppedResult.reason}</p>
    </div>
  }

  return <TypewriterInterface props={props} />
}

/** The interface in command line mode */
export function TypewriterInterface({props}) {
  let { t } = useTranslation()
  const ec = React.useContext(EditorContext)
  const gameId = React.useContext(GameIdContext)
  const editor = React.useContext(MonacoEditorContext)
  const model = editor.getModel()
  const uri = model.uri.toString()

  const gameInfo = useGetGameInfoQuery({game: gameId})
  const {worldId, levelId} = React.useContext(WorldLevelIdContext)
  let image: string = gameInfo.data?.worlds.nodes[worldId].image


  const [disableInput, setDisableInput] = React.useState<boolean>(false)
  const [loadingProgress, setLoadingProgress] = React.useState<number>(0)
  const { setDeletedChat, showHelp, setShowHelp } = React.useContext(DeletedChatContext)
  const {mobile} = React.useContext(PreferencesContext)
  const { proof, setProof, crashed, setCrashed, interimDiags } = React.useContext(ProofContext)
  const { setTypewriterInput } = React.useContext(InputModeContext)
  const { selectedStep, setSelectedStep } = React.useContext(SelectionContext)

  const proofPanelRef = React.useRef<HTMLDivElement>(null)
  // const config = useEventResult(ec.events.changedInfoviewConfig) ?? defaultInfoviewConfig;
  // const curUri = useEventResult(ec.events.changedCursorLocation, loc => loc?.uri);

  const rpcSess = useRpcSessionAtPos({uri: uri, line: 0, character: 0})

  /** Delete all proof lines starting from a given line.
  * Note that the first line (i.e. deleting everything) is `1`!
  */
  function deleteProof(line: number) {
    return (ev) => {
      let deletedChat: Array<GameHint> = []
      proof?.steps.slice(line).map((step, i) => {
        let filteredHints = filterHints(step.goals[0]?.hints, proof?.steps[i-1]?.goals[0]?.hints)

        // Only add these hidden hints to the deletion stack which were visible
        deletedChat = [...deletedChat, ...filteredHints.filter(hint => (!hint.hidden || showHelp.has(line + i)))]
      })
      setDeletedChat(deletedChat)

      // delete showHelp for deleted steps
      setShowHelp(new Set(Array.from(showHelp).filter(i => i < line - 1)))

      editor.executeEdits("typewriter", [{
        range: monaco.Selection.fromPositions(
          { lineNumber: line, column: 1 },
          editor.getModel().getFullModelRange().getEndPosition()
        ),
        text: '',
        forceMoveMarkers: false
      }])
      setSelectedStep(undefined)
      setTypewriterInput(proof?.steps[line].command)
      // Reload proof on deleting
      loadGoals(rpcSess, uri, setProof, setCrashed)
      ev.stopPropagation()
    }
  }

  function toggleSelectStep(line: number) {
    return (ev) => {
      if (mobile) {return}
      if (selectedStep == line) {
        setSelectedStep(undefined)
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

  return <div className="typewriter-interface">
    <RpcContext.Provider value={rpcSess}>
    <div className="content">
      <div className='world-image-container empty'>
        {image &&
          <img className="contain" src={path.join("data", gameId, image)} alt="" />
        }

      </div>
      <div className="tmp-pusher">
        {/* <div className="world-image-container empty">

        </div> */}
      </div>
      <div className='proof' ref={proofPanelRef}>
        <ExerciseStatement data={props.data} />
        {crashed ? <div>
          <p className="crashed_message">{t("Crashed! Go to editor mode and fix your proof! Last server response:")}</p>
          {interimDiags.map(diag => {
            const severityClass = diag.severity ? {
              [DiagnosticSeverity.Error]: 'error',
              [DiagnosticSeverity.Warning]: 'warning',
              [DiagnosticSeverity.Information]: 'information',
              [DiagnosticSeverity.Hint]: 'hint',
            }[diag.severity] : '';

            return <div>
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
                  {mobile && i == 0 && props.data?.introduction &&
                    <div className={`message information step-0${selectedStep === 0 ? ' selected' : ''}`} onClick={toggleSelectStep(0)}>
                      <Markdown>{props.data?.introduction}</Markdown>
                    </div>
                  }
                  {mobile &&
                    <Hints key={`hints-${i}`}
                      hints={filteredHints} showHidden={showHelp.has(i)} step={i}
                      selected={selectedStep} toggleSelection={toggleSelectStep(i)}/>
                  }
                  {/* <GoalsTabs proofStep={step} last={i == proof?.steps.length - (lastStepErrors ? 2 : 1)} onClick={toggleSelectStep(i)} onGoalChange={i == proof?.steps.length - 1 - withErr ? (n) => setDisableInput(n > 0) : (n) => {}}/> */}
                  {!(isLastStepWithErrors(proof, i)) &&
                    <GoalsTabs proofStep={step} last={i == proof?.steps.length - (lastStepHasErrors(proof) ? 2 : 1)} onClick={toggleSelectStep(i)} onGoalChange={i == proof?.steps.length - (lastStepHasErrors(proof) ? 2 : 1) ? (n) => setDisableInput(n > 0) : (n) => {}}/>
                  }
                  {mobile && i == proof?.steps.length - 1 &&
                    <MoreHelpButton />
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
                {props.level >= props.worldSize ?
                  <Button to={`/${gameId}`}>
                    <FontAwesomeIcon icon={faHome} />&nbsp;{t("Leave World")}
                  </Button>
                :
                  <Button to={`/${gameId}/world/${props.world}/level/${props.level + 1}`}>
                    Next&nbsp;<FontAwesomeIcon icon={faArrowRight} />
                  </Button>
                }
              </div>
            }
          </> : <CircularProgress variant="determinate" value={100*(1 - 1.024 ** (- loadingProgress))} />
        // note: since we don't know the total number of files,
        // we use a function which strictly monotonely increases towards `100` as `x → ∞`
        // The base is chosen at random s.t. we get roughly 91% for `x = 100`.
        }
      </div>
    </div>
    <Typewriter disabled={disableInput || !proof?.steps.length}/>
    </RpcContext.Provider>
  </div>
}
