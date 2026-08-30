import { useTranslation } from "react-i18next"
import { useGameTranslation } from "../../utils/translation"
import { useAtom } from "jotai"
import { gameIdAtom, levelIdAtom, worldIdAtom } from "../../store/location-atoms"
import { gameInfoAtom } from "../../store/query-atoms"
import { readWorldIntroAtom } from "../../store/progress-atoms"
import { mobileAtom } from "../../store/preferences-atoms"
import { useEffect, useRef } from "react"
import React from "react"
import { Hint } from "../hints"
import { FontAwesomeIcon } from "@fortawesome/react-fontawesome"
import { faArrowRight, faHome } from "@fortawesome/free-solid-svg-icons"
import { Button } from "../button"

/** Appears on the left side of the intro of a world */
export function IntroPanel() {
  let { t } = useTranslation()
  const { t : gT } = useGameTranslation()
  const [gameId, navigateToGame] = useAtom(gameIdAtom)
  const [worldId] = useAtom(worldIdAtom)
  const [{ data: gameInfo }] = useAtom(gameInfoAtom)
  const [, navigateToLevel] = useAtom(levelIdAtom)
  const [, readWorldIntro] = useAtom(readWorldIntroAtom)

  const [mobile] = useAtom(mobileAtom)

  let text: Array<string> = gT(gameInfo?.worlds?.nodes[worldId ?? ""]?.introduction ?? "").split(/\n(\s*\n)+/)

  const focusRef = useRef<HTMLButtonElement>()
  useEffect(() => {
   focusRef.current?.focus()
  }, [])

  return <div className="chat-panel">
    <div className="chat">
      {text?.filter(t => t.trim()).map(((t, i) =>
        <Hint key={`intro-p-${i}`}
          hint={{text: t, hidden: false, rawText: t, varNames: []}} step={0} selected={undefined} toggleSelection={undefined} />
      ))}
    </div>
    <div className={`button-row${mobile ? ' mobile' : ''}`}>
      {gameInfo?.worldSize?.[worldId ?? ""] == 0 ?
        <Button onClick={() => {if (gameId) navigateToGame(gameId)}}>
          <FontAwesomeIcon icon={faHome} />
          </Button> :
        <Button ref={focusRef} onClick={() => {readWorldIntro(); navigateToLevel(1)}}>
          {t("Start")}&nbsp;<FontAwesomeIcon icon={faArrowRight} />
        </Button>
      }
    </div>
  </div>
}
