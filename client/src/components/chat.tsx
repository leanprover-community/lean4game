import * as React from 'react'
import { useContext, useEffect, useRef, useState } from 'react'
import { useSelector } from 'react-redux'
import { useTranslation } from 'react-i18next'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faArrowRight } from '@fortawesome/free-solid-svg-icons'


import Markdown from './markdown'
import { Button } from './button'

import { changedReadIntro, selectCompleted, selectReadIntro } from '../state/progress'
import { useGetGameInfoQuery, useLoadLevelQuery } from '../state/api'
import { useAppDispatch, useAppSelector } from '../hooks'

import { ChatContext, GameIdContext, PageContext, PreferencesContext, ProofContext } from '../state/context'
import { GameHint, InteractiveGoalsWithHints } from './infoview/rpc_api'
import { lastStepHasErrors } from './infoview/goals'

import '../css/chat.css'

/** Split a string by double newlines and filters out empty segments. */
function splitIntro (intro : string) {
  return intro.split(/\n(\s*\n)+/).filter(t => t.trim())
}

/** Helper to check if a step has any hidden hints. */
function hasHiddenHints(step: InteractiveGoalsWithHints): boolean {
  return step?.goals[0]?.hints.some((hint) => hint.hidden)
}

/** Button which only appears if the current step has hidden hints that are not shown yet. */
export function MoreHelpButton({selected=null} : {selected?: number}) {

  const { t } = useTranslation()

  const { proof } = React.useContext(ProofContext)
  const { showHelp, setShowHelp } = React.useContext(ChatContext)

  let k = proof?.steps.length ?
    ((selected === null) ? (proof?.steps.length - (lastStepHasErrors(proof) ? 2 : 1)) : selected)
    : 0

  const activateHiddenHints = (ev) => {
    // If the last step (`k`) has errors, we want the hidden hints from the
    // second-to-last step to be affected
    if (!(proof?.steps.length)) {return <></>}

    // state must not be mutated, therefore we need to clone the set
    let tmp = new Set(showHelp)
    if (tmp.has(k)) {
      tmp.delete(k)
    } else {
      tmp.add(k)
    }
    setShowHelp(tmp)
    console.debug(`help: ${Array.from(tmp.values())}`)
  }

  if (hasHiddenHints(proof?.steps[k]) && !showHelp.has(k)) {
    return <Button to="" onClick={activateHiddenHints}>
      {t("Show more help!")}
    </Button>
  }
  return <></>
}

/** Placeholder that takes the same space as a button. */
function ButtonPlaceholder() {
  return <div className='btn-placeholder'/>
}

/** The buttons at the bottom of chat. */
export function ChatButtons ({counter=undefined, setCounter=()=>{}, introMessages=[]} : {
  counter?: number
  setCounter?: React.Dispatch<React.SetStateAction<number>>
  introMessages?: GameHintWithStep[]
}) {

  const { mobile } = useContext(PreferencesContext)
  const { gameId, worldId, levelId } = useContext(GameIdContext)
  const {setPage} = useContext(PageContext)
  const dispatch = useAppDispatch()
  const gameInfo = useGetGameInfoQuery({game: gameId})

  const readIntro = useSelector(selectReadIntro(gameId, worldId))

  return <div className="button-row">
    {!levelId && (readIntro || (counter >= introMessages.length) ?
      ((worldId || mobile) &&
        <>
          <ButtonPlaceholder />
          <Button className="btn"
              title=""
              to={worldId ? `/${gameId}/world/${worldId}/level/1` : ''}
              onClick={() => {
                if (!worldId) {
                  console.log('setting `readIntro` to true')
                  setPage(1)
                }
              }} >
            Start&nbsp;<FontAwesomeIcon icon={faArrowRight}/>
          </Button>
        </>
      )
      :
      <>
        <Button className="btn"
            title=""
            to=""
            onClick={() => {
              if (counter + 1 >= introMessages.length) {
                dispatch(changedReadIntro({game: gameId, world: worldId, readIntro: true}))
              }
              setCounter(counter + 1)
            }} >
          {"Read"}
        </Button>
        <Button className="btn"
            title=""
            to=""
            onClick={() => {
              dispatch(changedReadIntro({game: gameId, world: worldId, readIntro: true}))
              setCounter(introMessages.length)
            }} >
          Skip all
        </Button>
      </>
    )}
    { (worldId && levelId) ? <MoreHelpButton /> : <></> }
  </div>
}

/** Insert the variable names in a hint. We do this client-side to prepare
 * for i18n in the future. i.e. one should be able translate the `rawText`
 * and have the variables substituted just before displaying.
 */
function getHintText(hint: GameHint): string {
  const {gameId} = React.useContext(GameIdContext)
  let { t } = useTranslation()
  if (hint.rawText) {
    // Replace the variable names used in the hint with the ones used by the player
    // variable names are marked like `«{g}»` inside the text.
    return t(hint.rawText, {ns: gameId}).replaceAll(/«\{(.*?)\}»/g, ((_, v) =>
      // `hint.varNames` contains tuples `[oldName, newName]`
      (hint.varNames.find(x => x[0] == v))[1]))
  } else {
    // hints created in the frontend do not have a `rawText`
    // TODO: `hint.text` could be removed in theory.
    return t(hint.text, {ns: gameId})
  }
}

/** Bundling a hint with the proof-step it comes from. */
type GameHintWithStep = {
  hint: GameHint
  step?: number
  conclusion?: boolean
}

/** Filter hints to not show consequtive identical hints twice.
 * Hidden hints are not filtered.
 */
export function filterHints(hints: GameHint[], prevHints: GameHint[]): GameHint[] {
  if (!hints) {
    return []
  } else if (!prevHints) {
    return [...hints.filter((hint) => !hint.hidden), ...hints.filter((hint) => hint.hidden)]
  } else {
    return [...hints.filter((hint) => !hint.hidden &&
      (prevHints.find(x => (x.text == hint.text && x.hidden == hint.hidden)) === undefined)
    ), ...hints.filter((hint) => hint.hidden)]
  }
}

/** A hint as it is displayed in the chat. */
export function Hint({hint, step=null, conclusion=false} : GameHintWithStep) {
  const { levelId } = useContext(GameIdContext)
  const { selectedStep, setSelectedStep } = useContext(ChatContext)

  const { proof } = useContext(ProofContext)
  const { typewriterMode } = useContext(PageContext)

  function toggleSelection () {
    if (!levelId) {return}

    if (selectedStep !== null && selectedStep == step) {
      setSelectedStep(null)
    } else if (step < proof?.steps?.length) {
      setSelectedStep(step)
    }
  }

  // "Deleted hints" are marked in grey. They are used two-fold:
  // In typewriter, deleting parts of the proof stores the removed hints as `deletedChat`
  // until the next command is submitted; in editor, moving the cursor through the proof will
  // render all hints
  return <div className={`message ${conclusion ? 'success' : hint.hidden ? 'warning' : 'information'} step-${step}` +
      ((selectedStep !== null && step == selectedStep) ? ' selected' : '') +
      (step == proof?.steps?.length - (lastStepHasErrors(proof) ? 2 : 1) ? ' recent' : '') +
      (!conclusion && step >= (typewriterMode ? proof?.steps?.length : selectedStep+1) ? ' deleted-hint' : '') } onClick={toggleSelection}>
    <Markdown>{getHintText(hint)}</Markdown>
  </div>
}

/** A collection of hints. If the `counter` is defined, only the first elements will be
 * shown up to the value of the `counter`.
 *
 * Set `conclusion` to true to trigger different style and disable selecting/deleting.
 */
export function Hints({ hints, conclusion, counter=undefined } : {
  hints: GameHintWithStep[],
  conclusion?: boolean,
  counter?: number
}) {

  const { showHelp } = useContext(ChatContext)

  if (!hints) {
    return <></>
  }

  // NOTE: This builds on the fact that `.slice(0, undefined)` returns the whole array!
  // TODO: Should not use index as key.
  return <>
    { hints.slice(0, counter).map((hint, j) =>
      ((!hint.hint.hidden || showHelp.has(hint.step)) &&
        <Hint key={`hint-${hint.step}-${j}`} hint={hint.hint} step={hint.step} conclusion={conclusion} />
      )
    )}
    {/* { //showHelp.has(hint.step) &&
      hints.filter(hint => hint.hint.hidden).map((hint, j) =>
      <Hint
        key={`hidden-hint-${hint.step}-${j}`}
        hint={hint.hint}
        step={hint.step}
        conclusion={hint.conclusion} />
    )} */}
  </>
}

/** the panel showing the game's introduction text */
export function ChatPanel ({visible = true}) {

  let { t } = useTranslation()

  const { mobile } = useContext(PreferencesContext)
  const { gameId, worldId, levelId } = useContext(GameIdContext)

  const completed = useAppSelector(selectCompleted(gameId, worldId, levelId))

  const gameInfo = useGetGameInfoQuery({game: gameId})
  const levelInfo = useLoadLevelQuery({game: gameId, world: worldId, level: levelId})

  const [counter, setCounter] = useState(1)

  const [introText, setIntroText] = useState<Array<GameHintWithStep>>([])
  const [chatMessages, setChatMessages] = useState<Array<GameHintWithStep>>([])
  const { chatRef, deletedChat, showHelp, selectedStep } = useContext(ChatContext)
  const { proof } = useContext(ProofContext)

  const readIntro = useSelector(selectReadIntro(gameId, worldId))

  useEffect(() => {
    setCounter(1)
  }, [gameId, worldId, levelId])

  // load and display the correct intro text
  useEffect(() => {
    let messages: GameHintWithStep[] = []

    if (levelId > 0) {
      let introText = t(levelInfo.data?.introduction, {ns : gameId}).trim()
      let introHint: GameHintWithStep = {hint: {text: introText, hidden: false, rawText: introText }, step: 0}

      // playable level: show the level's intro
      if (levelInfo.data?.introduction) {
        setIntroText([introHint])
        // messages = messages.concat([introHint])
      }
      else {
        setIntroText([])
      }

      proof?.steps?.forEach((step, i) => {
        console.log("tesr")
        messages = messages.concat(filterHints(step.goals[0]?.hints, proof.steps[i-1]?.goals[0]?.hints).map(hint => ({hint: hint, step: i})))
      })

    } else {
      if (worldId) {
        let introText = t(gameInfo.data?.worlds.nodes[worldId].introduction, {ns: gameId}).trim()
        let introHints: GameHintWithStep[] = splitIntro(introText).map( txt => ({hint: {text: txt, hidden: false, rawText: txt }, step: 0}))

        // Level 0: show the world's intro
        if (gameInfo.data?.worlds.nodes[worldId].introduction) {
          // messages = messages.concat(introHints)
          setIntroText(introHints)
        } else {
          setIntroText([])
        }
      } else {
        let introText = t(gameInfo.data?.introduction, {ns : gameId}).trim()
        let introHints: GameHintWithStep[] = splitIntro(introText).map( txt => ({hint: {text: txt, hidden: false, rawText: txt }, step: 0}))

        // world overview: show the game's intro
        if (gameInfo.data?.introduction) {
          // messages = messages.concat(introHints)
          setIntroText(introHints)
        } else {
          setIntroText([])
        }
      }
    }
    console.log('chat messages:')
    console.log(messages)
    setChatMessages(messages)
  }, [gameInfo, levelInfo, gameId, worldId, levelId, proof])

  // Scroll the chat
  useEffect(() => {
    if (levelId > 0) {

      if (proof) {
        if (proof?.completed) {
          // proof currently completed: scroll down
          console.debug('scroll chat: down to conclusion')
          chatRef.current!.lastElementChild?.scrollIntoView({block: "center"})
        } else {
          // proof currently not completed: first message of last step
          let lastStep = proof?.steps.length - (lastStepHasErrors(proof) ? 2 : 1)
          console.debug(`scroll chat: first message of step ${lastStep}`)
          chatRef.current?.getElementsByClassName(`step-${lastStep}`)[0]?.scrollIntoView({block: "center"})
        }
      } else {
        // no proof available: scroll to top.
        console.debug(`scroll chat: top`)
        chatRef.current!.scrollTo(0,0)
      }
    } else {
      // introduction: scroll to last message
      console.debug('scroll chat: down')
      chatRef.current!.lastElementChild?.scrollIntoView({block: "center"})
    }
  }, [counter, introText, chatMessages, gameId, worldId, levelId])

  // Scroll down when new hidden hints are triggered
  useEffect(() => {
    if (levelId > 0) {
      let lastStep = proof?.steps.length - (lastStepHasErrors(proof) ? 2 : 1)
      if (showHelp.has(lastStep)) {
        console.debug('scroll chat: down to hidden hints')
        // TODO: last element of hidden hints?
        chatRef.current!.lastElementChild?.scrollIntoView({block: "center"})
      }
    }
  }, [showHelp, gameId, worldId, levelId])

  // Scroll to corresponding messages if selected step changes
  useEffect(() => {
    if (levelId > 0 && selectedStep !== null) {
      console.debug(`scroll chat: first message of selected step ${selectedStep}`)
      chatRef.current?.getElementsByClassName(`step-${selectedStep}`)[0]?.scrollIntoView({block: "center"})
      // Array.from(chatRef.current?.getElementsByClassName(`step-${selectedStep}`)).map((elem) => {
      //   elem.scrollIntoView({block: "center"})
      // })
    }
  }, [selectedStep, gameId, worldId, levelId])

  return <div className={`column chat-panel${visible ? '' : ' hidden'}`}>
    <div ref={chatRef} className="chat" >
      { gameInfo.error &&
        <div className="message error">
          Could not find the game!
        </div>
        }
      <Hints hints={introText} counter={readIntro ? undefined : counter}/>
      <Hints hints={chatMessages}/>
      {/* {proof?.steps.map((step, i) =>
        <Hints hints={step.goals[0]?.hints.map(hint => ({hint: hint, step: i}))}/>
      )} */}
      {/* <Hints hints={proof?.steps[proof?.steps?.length - 1]?.goals[0].hints.map(hint => ({hint: hint, step: proof?.steps?.length - 1}))} /> */}

      { deletedChat &&
        <Hints hints={deletedChat.map(hint => ({hint: hint, step: proof?.steps?.length}))} />
      }
      { completed && levelInfo.data?.conclusion &&
        <Hints hints={[{hint: {text: t("Level completed! 🎉"), rawText: t("Level completed! 🎉"), hidden: false}, step: proof?.steps?.length}, {hint: {text: levelInfo.data?.conclusion, rawText: levelInfo.data?.conclusion, hidden: false}, step: proof?.steps?.length} ]} conclusion={true} />
      }

      {/* {chatMessages.map(((t, i) =>
        t.trim() ?
          <Hint key={`intro-p-${i}`}
            hint={{text: t, hidden: false, rawText: t, varNames: []}}
            step={0} />
        : <></>
      ))} */}
    </div>
    { <ChatButtons counter={counter} setCounter={setCounter} introMessages={introText}/> }
  </div>
}
