import React from "react"
import { GameEditor } from "../infoview/GameEditor"

/** The center-piece of a playable level */
export function ExercisePanel({codeviewRef, visible=true}: {codeviewRef: React.MutableRefObject<HTMLDivElement>, visible?: boolean}) {
  return <div className={`exercise-panel exercise ${visible ? '' : 'hidden'}`}>
    <GameEditor codeviewRef={codeviewRef} />
  </div>
}
