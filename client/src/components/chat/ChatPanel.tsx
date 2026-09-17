import * as React from 'react'
import { useTranslation } from 'react-i18next'
import { useGameTranslation } from '../../utils/translation'
import { useEffect, useRef } from 'react'
import { useAtom } from 'jotai'
import { mobileAtom } from '../../store/preferences-atoms'
import { gameIdAtom, levelIdAtom } from '../../store/location-atoms'
import { levelInfoAtom } from '../../store/query-atoms'
import { deletedChatAtom, helpAtom, selectedStepAtom } from '../../store/chat-atoms'
import { proofAtom } from '../../store/editor-atoms'
import { DeletedHints, filterHints, Hint, Hints, MoreHelpButton } from '../hints'
import Markdown from 'react-markdown'
import { faArrowRight, faHome } from '@fortawesome/free-solid-svg-icons'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { Button } from '../button'

/** Appears on the left of playable levels */
export function ChatPanel({lastLevel, visible = true}: {lastLevel: boolean, visible: boolean}) {
  let { t } = useTranslation()
  const { t : gT } = useGameTranslation()
  const chatRef = useRef<HTMLDivElement>(null)
  const [mobile] = useAtom(mobileAtom)
  const [gameId, navigateToGame] = useAtom(gameIdAtom)
  const [levelId, navigateToLevel] = useAtom(levelIdAtom)
  const [{ data: levelInfo }] = useAtom(levelInfoAtom)
  const [help] = useAtom(helpAtom)
  const [proof] = useAtom(proofAtom)
  const [deletedChat] = useAtom(deletedChatAtom)
  const [selectedStep, setSelectedStep] = useAtom(selectedStepAtom)

  let k = proof?.steps.length ? proof?.steps.length - (lastStepHasErrors(proof) ? 2 : 1) : 0

  function toggleSelection(line: number) {
    return (ev: any) => {
      console.debug('toggled selection')
      if (selectedStep == line) {
        setSelectedStep(undefined)
      } else {
        setSelectedStep(line)
      }
    }
  }

  useEffect(() => {
    // TODO: For some reason this is always called twice
    console.debug('scroll chat')
    if (!mobile) {
      chatRef.current!.lastElementChild?.scrollIntoView() //scrollTo(0,0)
    }
  }, [proof, help])

  // Scroll to element if selection changes
  useEffect(() => {
    if (typeof selectedStep !== 'undefined') {
      Array.from(chatRef.current!.getElementsByClassName(`step-${selectedStep}`)).map((elem) => {
        elem.scrollIntoView({block: "center"})
      })
    }
  }, [selectedStep])

  // useEffect(() => {
  //   // // Scroll to top when loading a new level
  //   // // TODO: Thats the wrong behaviour probably
  //   // chatRef.current!.scrollTo(0,0)
  // }, [gameId, worldId, levelId])

  let introText: Array<string> = gT(levelInfo?.introduction ?? "").split(/\n(\s*\n)+/)

  const focusRef = useRef<HTMLButtonElement>()
  useEffect(() => {
   if (proof?.completed) {
     focusRef.current?.focus()
   }
  }, [!!proof?.completed])

  return <div className={`chat-panel ${visible ? '' : 'hidden'}`}>
    <div ref={chatRef} className="chat">
      {introText?.filter(it => it.trim()).map(((it, i) =>
        // Show the level's intro text as hints, too
        <Hint key={`intro-p-${i}`}
          hint={{text: it, hidden: false, rawText: it, varNames: []}} step={0} selected={selectedStep} toggleSelection={toggleSelection(0)} />
      ))}
      {proof?.steps.map((step, i) => {
        let filteredHints = filterHints(step.goals[0]?.hints, proof?.steps[i-1]?.goals[0]?.hints)
        if (step.goals.length > 0 && !isLastStepWithErrors(proof, i)) {
          return <Hints key={`hints-${i}`}
          hints={filteredHints} showHidden={help.has(i)} step={i}
          selected={selectedStep} toggleSelection={toggleSelection(i)} lastLevel={i == proof?.steps.length - 1}/>
        }
      })}

      {/* {modifiedHints.map((step, i) => {
        // It the last step has errors, it will have the same hints
        // as the second-to-last step. Therefore we should not display them.
        if (!(i == proof?.steps.length - 1 && withErr)) {
          // TODO: Should not use index as key.
          return <Hints key={`hints-${i}`}
            hints={step} showHidden={showHelp?.has(i)} step={i}
            selected={selectedStep} toggleSelection={toggleSelection(i)} lastLevel={i == proof?.steps.length - 1}/>
        }
      })} */}
      <DeletedHints hints={deletedChat}/>
      {proof?.completed &&
        <>
          <div className={`message information recent step-${k}${selectedStep == k ? ' selected' : ''}`} onClick={toggleSelection(k)}>
            {t("Level completed! 🎉")}
          </div>
          {levelInfo?.conclusion?.trim() &&
            <div className={`message information recent step-${k}${selectedStep == k ? ' selected' : ''}`} onClick={toggleSelection(k)}>
              <Markdown>{gT(levelInfo?.conclusion ?? "")}</Markdown>
            </div>
          }
        </>
      }
    </div>
    <div className="button-row">
      {proof?.completed && (lastLevel ?
        <Button ref={focusRef} onClick={() => {if (gameId) navigateToGame(gameId)}} >
          <FontAwesomeIcon icon={faHome} />&nbsp;{t("Home")}
        </Button> :
        <Button ref={focusRef} onClick={() => {if(levelId !== undefined) navigateToLevel(levelId + 1)}}  >
          {t("Next")}&nbsp;<FontAwesomeIcon icon={faArrowRight} />
        </Button>)
        }
      <MoreHelpButton selected={null} />
    </div>
  </div>
}

//FIXME: implement
function lastStepHasErrors(x: any) {return false}

//FIXME: implement
function isLastStepWithErrors(x: any, y: any) {return false}
