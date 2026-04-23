import { useAtom } from "jotai"
import { leanMonacoAtom, typewriterModeAtom } from "../../store/editor-atoms"
import React, { useEffect, useLayoutEffect, useRef } from "react"
import { ExerciseStatement } from "./ExerciseStatement"
import { Typewriter } from "./typewriter"

/**
 * Note: It is important that the `div` with `codeViewRef` is
 * always present, or the monaco editor cannot start.
 */
export function GameEditor({ codeviewRef } : { codeviewRef: React.MutableRefObject<HTMLDivElement> }) {
  const infoviewRef = useRef<HTMLDivElement>(null)
  const [leanMonaco] = useAtom(leanMonacoAtom)
  const [typewriterMode] = useAtom(typewriterModeAtom)

  useLayoutEffect(() => {
    leanMonaco?.setInfoviewElement(infoviewRef.current!)
  })

  return <>
    <ExerciseStatement showLeanStatement={true} />
    <div ref={codeviewRef} className='codeview' />
    <div className='infoview' ref={infoviewRef} />
    {typewriterMode && <Typewriter />}
  </>
}
