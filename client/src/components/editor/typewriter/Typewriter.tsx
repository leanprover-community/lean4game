import React, { useRef } from "react";
import { useAtom } from "jotai";
import { gameInfoAtom } from "../../../store/query-atoms";
import { gameIdAtom, worldIdAtom } from "../../../store/location-atoms";
import path from "node:path";
import { proofAtom } from "../../../store/editor-atoms";
import { ExerciseStatement } from "../ExerciseStatement";
import { ProofStep } from "./proof_step/ProofStep";
import { TypewriterCommandLine } from "./TypewriterCommandline";
import { LoadingIcon } from "../../utils";
import { CircularProgress } from "@mui/material";

/**
 * Der Typewriter bestehend aus Eingabezeile, Beweisschritten, Aufgabenstellung und Hintergrundbild
 */
export function Typewriter() {
  const [{ data: gameInfo }] = useAtom(gameInfoAtom)
  const [gameId] = useAtom(gameIdAtom)
  const [worldId] = useAtom(worldIdAtom)
  const [proof] = useAtom(proofAtom)

  const proofPanelRef = useRef<HTMLDivElement>(null)

  let image = gameInfo?.worlds?.nodes[worldId!]?.image

  return <div className="typewriter-canvas">
    <div className="typewriter-info">
      {image && <img className="world-image contain" src={path.join("data", gameId!, image)} alt="" />}
      <div className="pusher" />
      <div className='proof' ref={proofPanelRef}>
        <ExerciseStatement showLeanStatement={true} />
        {proof ? proof.steps.map((step, i) => <ProofStep key={i} step={step} idx={i} />)
      : <div className="centered-spinner"><CircularProgress /></div>}
      </div>
    </div>
    <TypewriterCommandLine />
  </div>
}
