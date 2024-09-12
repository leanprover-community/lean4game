import * as React from 'react'
import { useContext } from 'react'
import { useRef, useState, useEffect } from 'react'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faArrowRight, faHome, faWandMagicSparkles } from '@fortawesome/free-solid-svg-icons'
import { DiagnosticSeverity, PublishDiagnosticsParams, DocumentUri } from 'vscode-languageserver-protocol';
import { useTranslation } from 'react-i18next'
import * as monaco from 'monaco-editor'
import { ChatContext, GameIdContext, InputModeContext, MonacoEditorContext, PageContext, PreferencesContext, ProofContext } from '../../state/context';

import { RpcContext, WithRpcSessions, useRpcSessionAtPos } from '../../../../node_modules/lean4-infoview/src/infoview/rpcSessions';
import { useServerNotificationEffect } from '../../../../node_modules/lean4-infoview/src/infoview/util';

import '../../css/infoview.css'
import { useGetGameInfoQuery } from '../../state/api'
import { GameHint } from './Defs'
import { MoreHelpButton, filterHints } from '../chat'
import { isLastStepWithErrors, lastStepHasErrors, loadGoals } from '../infoview/goals'
import { getInteractiveDiagsAt, hasInteractiveErrors } from '../infoview/typewriter'
import { Errors } from '../infoview/messages'
import { Button, Markdown } from '../utils'
import { Command, GoalsTabs } from '../infoview/main'
import { CircularProgress } from '@mui/material'

/** The input field */
export function TypewriterInput({disabled}: {disabled?: boolean}) {
  let { t } = useTranslation()

  /** Reference to the hidden multi-line editor */
  // const editor = React.useContext(MonacoEditorContext)
  // const model = editor.getModel()
  // const uri = model.uri.toString()

  const [oneLineEditor, setOneLineEditor] = useState<monaco.editor.IStandaloneCodeEditor>(null)
  const [processing, setProcessing] = useState(false)

  // const {typewriterInput, setTypewriterInput} = React.useContext(InputModeContext)

  const inputRef = useRef()

  // // The context storing all information about the current proof
  const {proof, setProof, interimDiags, setInterimDiags, setCrashed} = React.useContext(ProofContext)

  // // state to store the last batch of deleted messages
  // const {setDeletedChat} = React.useContext(DeletedChatContext)

  // const rpcSess = React.useContext(RpcContext)

  // // Run the command
  // const runCommand = React.useCallback(() => {
  //   if (processing) {return}

  //   // TODO: Desired logic is to only reset this after a new *error-free* command has been entered
  //   setDeletedChat([])

  //   const pos = editor.getPosition()
  //   if (typewriterInput) {
  //     setProcessing(true)
  //     editor.executeEdits("typewriter", [{
  //       range: monaco.Selection.fromPositions(
  //         pos,
  //         editor.getModel().getFullModelRange().getEndPosition()
  //       ),
  //       text: typewriterInput.trim() + "\n",
  //       forceMoveMarkers: false
  //     }])
  //     setTypewriterInput('')
  //     // Load proof after executing edits
  //     loadGoals(rpcSess, uri, setProof, setCrashed)
  //   }

  //   editor.setPosition(pos)
  // }, [typewriterInput, editor])

  // useEffect(() => {
  //   if (oneLineEditor && oneLineEditor.getValue() !== typewriterInput) {
  //     oneLineEditor.setValue(typewriterInput)
  //   }
  // }, [typewriterInput])

  // /* Load proof on start/switching to typewriter */
  // useEffect(() => {
  //   loadGoals(rpcSess, uri, setProof, setCrashed)
  // }, [])

  // /** If the last step has an error, add the command to the typewriter. */
  // useEffect(() => {
  //   if (lastStepHasErrors(proof)) {
  //     setTypewriterInput(proof?.steps[proof?.steps.length - 1].command)
  //   }
  // }, [proof])

  // // React when answer from the server comes back
  // useServerNotificationEffect('textDocument/publishDiagnostics', (params: PublishDiagnosticsParams) => {
  //   if (params.uri == uri) {
  //     setProcessing(false)

  //     console.log('Received lean diagnostics')
  //     console.log(params.diagnostics)
  //     setInterimDiags(params.diagnostics)

  //     //loadGoals(rpcSess, uri, setProof)

  //     // TODO: loadAllGoals()
  //     if (!hasErrors(params.diagnostics)) {
  //       //setTypewriterInput("")
  //       editor.setPosition(editor.getModel().getFullModelRange().getEndPosition())
  //     }
  //   } else {
  //     // console.debug(`expected uri: ${uri}, got: ${params.uri}`)
  //     // console.debug(params)
  //   }
  //   // TODO: This is the wrong place apparently. Where do wee need to load them?
  //   // TODO: instead of loading all goals every time, we could only load the last one
  //   // loadAllGoals()
  // }, [uri]);

  // // // React when answer from the server comes back
  // // useServerNotificationEffect('$/game/publishDiagnostics', (params: GameDiagnosticsParams) => {
  // //   console.log('Received game diagnostics')
  // //   console.log(`diag. uri : ${params.uri}`)
  // //   console.log(params.diagnostics)

  // // }, [uri]);


  // useEffect(() => {
  //   const myEditor = monaco.editor.create(inputRef.current!, {
  //     value: typewriterInput,
  //     language: "lean4cmd",
  //     quickSuggestions: false,
  //     lightbulb: {
  //       enabled: true
  //     },
  //     unicodeHighlight: {
  //         ambiguousCharacters: false,
  //     },
  //     automaticLayout: true,
  //     minimap: {
  //       enabled: false
  //     },
  //     lineNumbers: 'off',
  //     tabSize: 2,
  //     glyphMargin: false,
  //     folding: false,
  //     lineDecorationsWidth: 0,
  //     lineNumbersMinChars: 0,
  //     'semanticHighlighting.enabled': true,
  //     overviewRulerLanes: 0,
  //     hideCursorInOverviewRuler: true,
  //     scrollbar: {
  //       vertical: 'hidden',
  //       horizontalScrollbarSize: 3
  //     },
  //     overviewRulerBorder: false,
  //     theme: 'vs-code-theme-converted',
  //     contextmenu: false
  //   })

  //   setOneLineEditor(myEditor)

  //   const abbrevRewriter = new AbbreviationRewriter(new AbbreviationProvider(), myEditor.getModel(), myEditor)

  //   return () => {abbrevRewriter.dispose(); myEditor.dispose()}
  // }, [])

  // useEffect(() => {
  //   if (!oneLineEditor) return
  //   // Ensure that our one-line editor can only have a single line
  //   const l = oneLineEditor.getModel().onDidChangeContent((e) => {
  //     const value = oneLineEditor.getValue()
  //     setTypewriterInput(value)
  //     const newValue = value.replace(/[\n\r]/g, '')
  //     if (value != newValue) {
  //       oneLineEditor.setValue(newValue)
  //     }
  //   })
  //   return () => { l.dispose() }
  // }, [oneLineEditor, setTypewriterInput])

  // useEffect(() => {
  //   if (!oneLineEditor) return
  //   // Run command when pressing enter
  //   const l = oneLineEditor.onKeyUp((ev) => {
  //     if (ev.code === "Enter") {
  //       runCommand()
  //     }
  //   })
  //   return () => { l.dispose() }
  // }, [oneLineEditor, runCommand])

  // // BUG: Causes `file closed` error
  // //TODO: Intention is to run once when loading, does that work?
  // useEffect(() => {
  //   console.debug(`time to update: ${uri} \n ${rpcSess}`)
  //   console.debug(rpcSess)
  //   // console.debug('LOAD ALL GOALS')
  //   // TODO: loadAllGoals()
  // }, [rpcSess])

  /** Process the entered command */
  const handleSubmit : React.FormEventHandler<HTMLFormElement> = (ev) => {
    // ev.preventDefault()
    // runCommand()
  }

  // do not display if the proof is completed (with potential warnings still present)
  return <div className={`typewriter-cmd${proof?.completedWithWarnings ? ' hidden' : ''}${disabled ? ' disabled' : ''}`}>
      <form onSubmit={handleSubmit}>
        <div className="typewriter-input-wrapper">
          <div ref={inputRef} className="typewriter-input" />
        </div>
        <button type="submit" disabled={processing} className="btn btn-inverted">
          <FontAwesomeIcon icon={faWandMagicSparkles} />&nbsp;{t("Execute")}
        </button>
      </form>
    </div>
}

export function TypewriterInterFace() {
  let { t } = useTranslation()
  const {gameId, worldId, levelId} = useContext(GameIdContext)
  const editor = useContext(MonacoEditorContext)
  const model = editor.getModel()
  const uri = model.uri.toString()

  const gameInfo = useGetGameInfoQuery({game: gameId})
  let image: string = gameInfo.data?.worlds.nodes[worldId].image


  const [disableInput, setDisableInput] = useState<boolean>(false)
  const [loadingProgress, setLoadingProgress] = useState<number>(0)
  const { selectedStep, setSelectedStep, setDeletedChat, showHelp, setShowHelp } = useContext(ChatContext)
  const {mobile} = useContext(PreferencesContext)
  const { proof, setProof, crashed, setCrashed, interimDiags } = useContext(ProofContext)
  const { setTypewriterInput } = useContext(PageContext)

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
      setSelectedStep(null)
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

  return <div className="typewriter-interface">
    <RpcContext.Provider value={rpcSess}>
      <div className="content">
        {/* <div className='world-image-container empty'>
          {image &&
            <img className="contain" src={path.join("data", gameId, image)} alt="" />
          }

        </div> */}
        {/* <div className="tmp-pusher">
          <div className="world-image-container empty">

          </div>
        </div> */}
        <div className='proof' ref={proofPanelRef}>
          {/* <ExerciseStatement /> */}
          {crashed ? <div>
            <p className="crashed_message">{t("Crashed! Go to editor mode and fix your proof! Last server response:")}</p>
            {interimDiags.map(diag => {
              const severityClass = diag.severity ? {
                [DiagnosticSeverity.Error]: 'error',
                [DiagnosticSeverity.Warning]: 'warning',
                [DiagnosticSeverity.Information]: 'information',
                [DiagnosticSeverity.Hint]: 'hint',
              }[diag.severity] : '';

              return <div key={diag.message} >
                <div className={`${severityClass} ml1 message`}>
                  <p className="mv2">{t("Line")}&nbsp;{diag.range.start.line}, {t("Character")}&nbsp;{diag.range.start.character}</p>
                  <pre className="font-code pre-wrap">
                    {diag.message}as React
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
                    {i > 0 && <>
                      <Command proof={proof} i={i} deleteProof={deleteProof(i)} />
                      <Errors errors={step.diags} typewriterMode={true} />
                    </>}
                    {mobile && i == 0 && props.data?.introduction &&
                      <div className={`message information step-0${selectedStep === 0 ? ' selected' : ''}`} onClick={toggleSelectStep(0)}>
                        <Markdown>{props.data?.introduction}</Markdown>
                      </div>
                    }
                    {mobile &&
                      <Hints key={`hints-${i}`}
                        hints={filteredHints.map(hint => ({hint: hint, step: i}))} />
                    }
                    {/* <GoalsTabs proofStep={step} last={i == proof?.steps.length - (lastStepErrors ? 2 : 1)} onClick={toggleSelectStep(i)} onGoalChange={i == proof?.steps.length - 1 - withErr ? (n) => setDisableInput(n > 0) : (n) => {}}/> */}
                    {!(isLastStepWithErrors(proof, i)) &&
                      <GoalsTabs goals={step.goals} last={i == proof?.steps.length - (lastStepHasErrors(proof) ? 2 : 1)} onClick={toggleSelectStep(i)} onGoalChange={i == proof?.steps.length - (lastStepHasErrors(proof) ? 2 : 1) ? (n) => setDisableInput(n > 0) : (n) => {}}/>
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
                      <FontAwesomeIcon icon={faHome} />&nbsp;{t("Home")}
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
      {/* <Typewriter disabled={disableInput || !proof?.steps.length}/> */}
      <TypewriterInput />
    </RpcContext.Provider>
  </div>
}
