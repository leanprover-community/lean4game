/* Partly copied from https://github.com/leanprover/vscode-lean4/blob/master/lean4-infoview/src/infoview/main.tsx */

import * as React from 'react';
import type { DidCloseTextDocumentParams, DidChangeTextDocumentParams, Location, DocumentUri } from 'vscode-languageserver-protocol';

import 'tachyons/css/tachyons.css';
import '@vscode/codicons/dist/codicon.css';
import '../../../../node_modules/lean4-infoview/src/infoview/index.css';
import './infoview.css'

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
import { LevelInfo } from '../../state/api';
import { changedInventory, levelCompleted, selectCompleted, selectInventory } from '../../state/progress';
import Markdown from '../markdown';

import { Infos } from './infos';
import { AllMessages, Errors, WithLspDiagnosticsContext } from './messages';
import { Goal } from './goals';
import { DeletedChatContext, InputModeContext, MobileContext, MonacoEditorContext, ProofContext, ProofStep, SelectionContext } from './context';
import { Typewriter, hasErrors, hasInteractiveErrors } from './typewriter';
import { InteractiveDiagnostic } from '@leanprover/infoview/*';
import { Button } from '../button';
import { CircularProgress } from '@mui/material';
import { GameHint } from './rpc_api';
import { store } from '../../state/store';
import { Hints } from '../hints';

/** Wrapper for the two editors. It is important that the `div` with `codeViewRef` is
 * always present, or the monaco editor cannot start.
 */
export function DualEditor({ level, codeviewRef, levelId, worldId, worldSize }) {
  const ec = React.useContext(EditorContext)
  const { typewriterMode } = React.useContext(InputModeContext)
  return <>
    <div className={typewriterMode ? 'hidden' : ''}>
      <ExerciseStatement data={level} />
      <div ref={codeviewRef} className={'codeview'}></div>
    </div>
    {ec ?
      <DualEditorMain worldId={worldId} levelId={levelId} level={level} worldSize={worldSize} /> :
      // TODO: Style this if relevant.
      <>
        <p>Editor is starting up...</p>
        <CircularProgress />
      </>
    }
  </>
}

/** The part of the two editors that needs the editor connection first */
function DualEditorMain({ worldId, levelId, level, worldSize }: { worldId: string, levelId: number, level: LevelInfo, worldSize: number }) {
  const ec = React.useContext(EditorContext)
  const gameId = React.useContext(GameIdContext)
  const { typewriterMode } = React.useContext(InputModeContext)

  // Mark level as completed when server gives notification
  const dispatch = useAppDispatch()
  useServerNotificationEffect(
    '$/game/completed',
    (params: any) => {
      if (ec.events.changedCursorLocation.current &&
        ec.events.changedCursorLocation.current.uri === params.uri) {
        dispatch(levelCompleted({ game: gameId, world: worldId, level: levelId }))

        // On completion, add the names of all new items to the local storage
        let newTiles = [
          ...level?.tactics,
          ...level?.lemmas,
          ...level?.definitions
        ].filter((tile) => tile.new).map((tile) => tile.name)

        let inv: string[] = selectInventory(gameId)(store.getState())

        // add new items and remove duplicates
        let newInv = [...inv, ...newTiles].filter((item, i, array) => array.indexOf(item) == i)

        dispatch(changedInventory({ game: gameId, inventory: newInv }))
      }
    }, [level]
  )

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
              {typewriterMode ?
                <TypewriterInterface world={worldId} level={levelId} data={level} worldSize={worldSize}/>
                :
                <Main key={`${worldId}/${levelId}`} world={worldId} level={levelId} />
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
 */
function ExerciseStatement({ data }) {
  if (!data?.descrText) { return <></> }
  return <div className="exercise-statement"><Markdown>
    {(data?.statementName ? `**Theorem** \`${data?.statementName}\`: ` : data?.descrText && "**Exercise**: ") + `${data?.descrText}`}
  </Markdown></div>
}

// TODO: This is only used in `EditorInterface`
// while `TypewriterInterface` has this copy-pasted in.
export function Main(props: { world: string, level: number }) {
  const ec = React.useContext(EditorContext);
  const gameId = React.useContext(GameIdContext)

  const completed = useAppSelector(selectCompleted(gameId, props.world, props.level))

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
    ret = <p>Waiting for Lean server to start...</p>
  } else if (serverStoppedResult) {
    ret = <div><p>{serverStoppedResult.message}</p><p className="error">{serverStoppedResult.reason}</p></div>
  } else {
    ret = <div className="infoview vscode-light">
      {completed && <div className="level-completed">Level completed! 🎉</div>}
      <Infos />
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
function Command({ command, deleteProof }: { command: string, deleteProof: any }) {
  // The first step will always have an empty command
  if (!command) { return <></> }
  return <div className="command">
    <div className="command-text">{command}</div>
    <Button to="" className="undo-button btn btn-inverted" title="Delete this and future commands" onClick={deleteProof}>
      <FontAwesomeIcon icon={faDeleteLeft} />&nbsp;Delete
    </Button>
  </div>
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
function GoalsTabs({ proofStep, last, onClick, onGoalChange=(n)=>{}}: { proofStep: ProofStep, last : boolean, onClick? : any, onGoalChange?: (n?: number) => void }) {

  const [selectedGoal, setSelectedGoal] = React.useState<number>(0)

  return <div className="goal-tabs" onClick={onClick}>
    <div className={`tab-bar ${last ? 'current' : ''}`}>
      {proofStep.goals.map((goal, i) => (
        // TODO: Should not use index as key.
        <div key={`proof-goal-${i}`} className={`tab ${i == (selectedGoal) ? "active" : ""}`} onClick={(ev) => { onGoalChange(i); setSelectedGoal(i); ev.stopPropagation() }}>
          {i ? `Goal ${i + 1}` : "Active Goal"}
        </div>
      ))}
    </div>
    <div className="goal-tab vscode-light">
      <Goal typewriter={false} filter={goalFilter} goal={proofStep.goals[selectedGoal]} />
    </div>
  </div>
}

/** The interface in command line mode */
export function TypewriterInterface(props: { world: string, level: number, data: LevelInfo, worldSize: number }) {

  const ec = React.useContext(EditorContext)
  const editor = React.useContext(MonacoEditorContext)
  const model = editor.getModel()
  const uri = model.uri.toString()
  const gameId = React.useContext(GameIdContext)
  const { proof } = React.useContext(ProofContext)
  const { selectedStep, setSelectedStep } = React.useContext(SelectionContext)
  const { setDeletedChat, showHelp, setShowHelp } = React.useContext(DeletedChatContext)

  const {mobile} = React.useContext(MobileContext)

  const proofPanelRef = React.useRef<HTMLDivElement>(null)

  const [disableInput, setDisableInput] = React.useState<boolean>(false)

  /** Delete all proof lines starting from a given line.
   * Note that the first line (i.e. deleting everything) is `1`!
   */
  function deleteProof(line: number) {
    return (ev) => {
      let deletedChat: Array<GameHint> = []
      proof.slice(line).map((step, i) => {
        // Only add these hidden hints to the deletion stack which were visible
        deletedChat = [...deletedChat, ...step.hints.filter(hint => (!hint.hidden || showHelp.has(line + i)))]
      })
      setDeletedChat(deletedChat)

      editor.executeEdits("typewriter", [{
        range: monaco.Selection.fromPositions(
          { lineNumber: line, column: 1 },
          editor.getModel().getFullModelRange().getEndPosition()
        ),
        text: '',
        forceMoveMarkers: false
      }])
      setSelectedStep(undefined)
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
    if (proof?.length > 1) {
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

  const completed = useAppSelector(selectCompleted(gameId, props.world, props.level))

  const config = useEventResult(ec.events.changedInfoviewConfig) ?? defaultInfoviewConfig;

  const curUri = useEventResult(ec.events.changedCursorLocation, loc => loc?.uri);

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

  if (!serverVersion) { return <p>Waiting for Lean server to start...</p> }
  if (serverStoppedResult) {
    return <div>
      <p>{serverStoppedResult.message}</p>
      <p className="error">{serverStoppedResult.reason}</p>
    </div>
  }

  // TODO: This about hidden hints is all copied from `level.tsx`. Can we move that into `hints.tsx`?

  // If the last step has errors, we want to treat it as if it is part of the second-to-last step
  let k = proof.length - 1
  let withErr = hasInteractiveErrors(proof[k]?.errors) ? 1 : 0

  const activateHiddenHints = (ev) => {
    // If the last step (`k`) has errors, we want the hidden hints from the
    // second-to-last step to be affected
    if (!(proof.length)) {return}

    // state must not be mutated, therefore we need to clone the set
    let tmp = new Set(showHelp)
    if (tmp.has(k - withErr)) {
      tmp.delete(k - withErr)
    } else {
      tmp.add(k - withErr)
    }
    setShowHelp(tmp)
    console.debug(`help: ${Array.from(tmp.values())}`)
  }

  function hasHiddenHints(i : number): boolean {
    let step = proof[i]

    // For example if the proof isn't loaded yet
    if(!step) {return false}

    return step.hints.some((hint) => hint.hidden)
  }

  let lastStepErrors = proof.length ? hasInteractiveErrors(proof[proof.length - 1].errors) : false

  // TODO: does the position matter at all?
  const rpcSess = useRpcSessionAtPos({uri: uri, line: 0, character: 0})

  return <div className="typewriter-interface">
    <RpcContext.Provider value={rpcSess}>
    <div className="content">
      <div className="tmp-pusher">
        {!proof.length &&
          <CircularProgress />
        }
      </div>
      <div className='proof' ref={proofPanelRef}>
        <ExerciseStatement data={props.data} />
        {proof.length ?
          <>
            {proof.map((step, i) => {
              if (i == proof.length - 1 && lastStepErrors) {
                // if the last command contains an error, we only display the errors but not the
                // entered command as it is still present in the command line.
                // TODO: Should not use index as key.
                return <div key={`proof-step-${i}`}>
                  <Errors errors={step.errors} typewriterMode={true} />
                </div>
              } else {
                return <div key={`proof-step-${i}`} className={`step step-${i}` + (selectedStep == i ? ' selected' : '')}>
                  <Command command={step.command} deleteProof={deleteProof(i)} />
                  <Errors errors={step.errors} typewriterMode={true} />
                  {mobile && i == 0 && props.data?.introduction &&
                    <div className={`message information step-0${selectedStep === 0 ? ' selected' : ''}`} onClick={toggleSelectStep(0)}>
                      <Markdown>{props.data?.introduction}</Markdown>
                    </div>
                  }
                  {mobile && <>
                    <Hints key={`hints-${i}`}
                      hints={step.hints} showHidden={showHelp.has(i)} step={i}
                      selected={selectedStep} toggleSelection={toggleSelectStep(i)}/>
                    {i == proof.length - 1 && hasHiddenHints(proof.length - 1) && !showHelp.has(k - withErr) &&
                      <Button className="btn btn-help" to="" onClick={activateHiddenHints}>
                        Show more help!
                      </Button>
                    }
                  </>
                  }
                  <GoalsTabs proofStep={step} last={i == proof.length - (lastStepErrors ? 2 : 1)} onClick={toggleSelectStep(i)} onGoalChange={i == proof.length - 1 - withErr ? (n) => setDisableInput(n > 0) : (n) => {}}/>
                  {/* Show a message that there are no goals left */}
                  {!step.goals.length && (
                    <div className="message information">
                      {completed ?
                        <p>Level completed! 🎉</p> :
                        <p>
                          <b>no goals left</b><br />
                          <i>This probably means you solved the level with warnings or Lean encountered a parsing error.</i>
                        </p>
                      }
                    </div>
                  )}
                </div>
              }
            })}
            {mobile && completed &&
              <div className="button-row">
                {props.level >= props.worldSize ?
                  <Button to={`/${gameId}`}>
                    <FontAwesomeIcon icon={faHome} />&nbsp;Leave World
                  </Button>
                :
                  <Button to={`/${gameId}/world/${props.world}/level/${props.level + 1}`}>
                    Next&nbsp;<FontAwesomeIcon icon={faArrowRight} />
                  </Button>
                }
              </div>
            }
          </> : <></>
        }
      </div>
    </div>
    <Typewriter hidden={!withErr && proof[proof.length - 1]?.goals.length == 0} disabled={disableInput}/>
    </RpcContext.Provider>
  </div>
}
