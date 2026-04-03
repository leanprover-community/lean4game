import React, { useEffect, useRef, useState } from "react";

import "../../css/typewriter.css"
import { useTranslation } from "react-i18next";
import { FontAwesomeIcon } from "@fortawesome/react-fontawesome";
import { faWandMagicSparkles } from "@fortawesome/free-solid-svg-icons";
import { useAtom } from "jotai";
import { gameInfoAtom } from "../../store/query-atoms";
import { gameIdAtom, worldIdAtom } from "../../store/location-atoms";
import path from "node:path";
import { proofAtom } from "../../store/editor-atoms";
import { ExerciseStatement } from "./ExerciseStatement";
import { ProofStep } from "./ProofStep";

/**
 * Der Typewriter bestehend aus Eingabezeile, Beweisschritten, Aufgabenstellung und Hintergrundbild
 */
export function Typewriter() {
  const [{ data: gameInfo }] = useAtom(gameInfoAtom)
  const [gameId, navigateToGame] = useAtom(gameIdAtom)
  const [worldId] = useAtom(worldIdAtom)
  const [proof, setProof ] = useAtom(proofAtom)

  const proofPanelRef = useRef<HTMLDivElement>(null)

  let image = gameInfo?.worlds?.nodes[worldId!]?.image

  return <div className="typewriter-canvas">
    <div className="typewriter-info">
      {image && <img className="world-image contain" src={path.join("data", gameId!, image)} alt="" />}
      <div className="pusher" />
      <div className='proof' ref={proofPanelRef}>
        <ExerciseStatement showLeanStatement={true} />
        {proof?.steps.map((step, i) => <ProofStep step={step} idx={i} />)}
      </div>
    </div>
    <TypewriterCommandLine />
  </div>
}

/** The input field */
export function TypewriterCommandLine() {
  let { t } = useTranslation()
  const oneLineEditorRef = useRef<any>(null)
  const [typewriterContent, setTypewriterContent] = useState("")

  /** Process the entered command */
  const handleSubmit : React.FormEventHandler<HTMLFormElement> = (ev) => {
    ev.preventDefault()
    // runCommand()
  }

  // do not display if the proof is completed (with potential warnings still present)
  return <div className="typewriter">
      <form onSubmit={handleSubmit}>
        <div className="typewriter-input-wrapper">
          <div className="typewriter-input" />
        </div>
        <button type="submit" disabled={false /* TODO */} className="btn btn-inverted">
          <FontAwesomeIcon icon={faWandMagicSparkles} />&nbsp;{t("Execute")}
        </button>
      </form>
    </div>
}
