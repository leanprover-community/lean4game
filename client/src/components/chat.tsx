import * as React from 'react'
import { PageContext, PreferencesContext } from './infoview/context'
import { GameIdContext } from '../app'
import { useTranslation } from 'react-i18next'
import { useAppDispatch } from '../hooks'
import { Hint } from './hints'
import { Button } from './button'
import { changedOpenedIntro } from '../state/progress'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faArrowRight } from '@fortawesome/free-solid-svg-icons'
import { useGetGameInfoQuery, useLoadLevelQuery } from '../state/api'
import { useContext, useEffect, useRef, useState } from 'react'
import '../css/level.css'
import '../css/chat.css'

/** Split a string by double newlines and filters out empty segments. */
function splitIntro (intro : string) {
  return intro.split(/\n(\s*\n)+/).filter(t => t.trim())
}

/** The buttons at the bottom of chat */
export function ChatButtons () {

  const { gameId, worldId, levelId } = useContext(GameIdContext)
  const {setPage} = useContext(PageContext)
  const dispatch = useAppDispatch()
  const gameInfo = useGetGameInfoQuery({game: gameId})

  return <div className="button-row">
    {(!worldId || !levelId) &&
      // Start button appears only on world selection and level 0.
      <Button className="btn"
          title=""
          to={worldId ? `/${gameId}/world/${worldId}/level/1` : ''}
          onClick={() => {
            if (!worldId) {
              console.log('setting `openedIntro` to true')
              setPage(1)
              dispatch(changedOpenedIntro({game: gameId, openedIntro: true}))
            }
          }} >
        Start&nbsp;<FontAwesomeIcon icon={faArrowRight}/>
      </Button>
    }
  </div>
}

/** the panel showing the game's introduction text */
export function ChatPanel ({visible = true}) {

  let { t } = useTranslation()
  const chatRef = useRef<HTMLDivElement>(null)

  const { mobile } = useContext(PreferencesContext)
  const { gameId, worldId, levelId } = useContext(GameIdContext)

  const gameInfo = useGetGameInfoQuery({game: gameId})
  const levelInfo = useLoadLevelQuery({game: gameId, world: worldId, level: levelId})

  let [chatMessages, setChatMessages] = useState<Array<string>>([])

  // Effect to clear chat and display the correct intro text
  useEffect(() => {
    if (levelId > 0) {
      // playable level: show the level's intro
      if (levelInfo.data?.introduction) {
        setChatMessages([t(levelInfo.data?.introduction, {ns : gameId})])
      }
      else {
        setChatMessages([])
      }
    } else {
      if (worldId) {
        // Level 0: show the world's intro
        if (gameInfo.data?.worlds.nodes[worldId].introduction) {
          setChatMessages(splitIntro(t(gameInfo.data?.worlds.nodes[worldId].introduction, {ns: gameId})))
        } else {
          setChatMessages([])
        }
      } else {
        // world overview: show the game's intro
        if (gameInfo.data?.introduction) {
          setChatMessages(splitIntro(t(gameInfo.data?.introduction, {ns : gameId})))
        } else {
          setChatMessages([])
        }
      }
    }
  }, [gameInfo, levelInfo, gameId, worldId, levelId])

  return <div className={`column chat-panel${visible ? '' : ' hidden'}`}>
    <div ref={chatRef} className="chat">

      {chatMessages.map(((t, i) =>
        t.trim() ?
          <Hint key={`intro-p-${i}`}
            hint={{text: t, hidden: false, rawText: t, varNames: []}}
            step={0} selected={null} toggleSelection={undefined} />
        : <></>
      ))}
    </div>
    { mobile && <ChatButtons /> }
  </div>
}
