import path from 'path';
import React from "react"
import * as monaco from 'monaco-editor/esm/vs/editor/editor.api.js'

import { useAtom } from "jotai"
import { useTranslation } from "react-i18next"
import { gameIdAtom, levelIdAtom, worldIdAtom } from "../../store/location-atoms"
import { gameInfoAtom } from "../../store/query-atoms"
import { deletedChatAtom, helpAtom, selectedStepAtom } from "../../store/chat-atoms"
import { mobileAtom } from "../../store/preferences-atoms"
import { crashedAtom, editorConnectionAtom, interimDiagsAtom, leanMonacoEditorAtom, proofAtom, rpcSessionAtPosAtom, typewriterContentAtom } from "../../store/editor-atoms"
import { Goal, isLastStepWithErrors, lastStepHasErrors, loadGoals } from "../../../../infoview/goals"
import { filterHints, Hint, Hints, MoreHelpButton } from "../hints"
import { GameHint } from "../infoview/types"
import { ExerciseStatement } from "../infoview/ExerciseStatement"
import { useRpcSessionAtPos } from "lean4monaco/dist/vscode-lean4/lean4-infoview/src/infoview/rpcSessions"
import { useServerNotificationEffect } from "lean4monaco/dist/vscode-lean4/lean4-infoview/src/infoview/util"
import { DiagnosticSeverity } from 'vscode-languageclient';
import { getInteractiveDiagsAt, hasInteractiveErrors } from "../../../../infoview/typewriter"
import { Button } from '../button';
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faArrowRight, faDeleteLeft, faHome } from "@fortawesome/free-solid-svg-icons"
import { InteractiveGoalsWithHints, ProofState } from "../../api/rpc_api"
import { Errors } from '../infoview/messages/Error'
import { CircularProgress } from '@mui/material';
import { Typewriter } from '../infoview/typewriter';
import { IconProp } from '@fortawesome/fontawesome-svg-core';


/** The interface in command line mode */
export function TypewriterInterface() {
  let { t } = useTranslation()
  const [editorConnection, _] = useAtom(editorConnectionAtom)//React.useContext(EditorContext)
  const [gameId, navigateToGame] = useAtom(gameIdAtom)
  const [worldId] = useAtom(worldIdAtom)
  const [levelId, navigateToLevel] = useAtom(levelIdAtom)
  const [{ data: gameInfo }] = useAtom(gameInfoAtom)
  const [help, setHelp] = useAtom(helpAtom)

  const [editor] = useAtom(leanMonacoEditorAtom)//React.useContext(MonacoEditorContext)
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
  const [rpcSession, setRpcSession] = useAtom(rpcSessionAtPosAtom)

  // Set the RPC session in the atom
  React.useEffect(() => {
    setRpcSession(rpcSess);
  }, [rpcSess, setRpcSession]);

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
    return (ev: any) => {
      let deletedChat: Array<GameHint> = []
      proof?.steps.slice(line).map((step, i) => {
        let filteredHints = filterHints(step.goals[0]?.hints, proof?.steps[i-1]?.goals[0]?.hints)

        // Only add these hidden hints to the deletion stack which were visible
        deletedChat = [...deletedChat, ...filteredHints.filter(hint => (!hint.hidden || help.has(line + i)))]
      })
      setDeletedChat(deletedChat)

      // delete showHelp for deleted steps
      setHelp(new Set(Array.from(help).filter(i => i < line - 1)))

      editor!.executeEdits("typewriter", [{
        range: monaco.Selection.fromPositions(
          { lineNumber: line, column: 1 },
          editor!.getModel()?.getFullModelRange().getEndPosition()
        ),
        text: '',
        forceMoveMarkers: false
      }])
      setSelectedStep(undefined)
      setTypewriter(proof?.steps[line].command ?? "")
      // Reload proof on deleting
      loadGoals(rpcSess, uri, worldId!, levelId!, setProof, setCrashed)
      ev.stopPropagation()
    }
  }

  function toggleSelectStep(line: number) {
    return (ev: any) => {
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
    if (proof?.steps?.length && proof?.steps?.length > 1) {
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
      Array.from(proofPanelRef.current!.getElementsByClassName(`step-${selectedStep}`)).map((elem) => {
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
        {((crashed && (interimDiags.length > 0 || proof!.steps.length > 0))) ? <div>
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
    <Typewriter/>
  </div>
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

const goalFilter = {
  reverse: false,
  showType: true,
  showInstance: true,
  showHiddenAssumption: true,
  showLetValue: true
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
