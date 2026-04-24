import React, { MutableRefObject, useEffect, useRef, useState } from "react";

import "../../css/typewriter.css"
import { useTranslation } from "react-i18next";
import { FontAwesomeIcon } from "@fortawesome/react-fontawesome";
import { faWandMagicSparkles } from "@fortawesome/free-solid-svg-icons";
import { useAtom, useSetAtom } from "jotai";
import { gameInfoAtom } from "../../store/query-atoms";

import { DiagnosticSeverity, PublishDiagnosticsParams, DocumentUri } from 'vscode-languageserver-protocol';
import * as monaco from 'monaco-editor'
import { levelIdAtom, gameIdAtom, worldIdAtom } from "../../store/location-atoms";
import { leanMonacoEditorAtom, typewriterContentAtom, interimDiagsAtom, crashedAtom, leanMonacoEditorModelAtom, leanMonacoEditorUriAtom, hasLeanMonacoEditorAtom, lastProofStepErrorCommandAtom, restoreErrorCommandEffect, oneLineEditorAtom, syncTypewriterToEditorEffect, syncEditorPositionEffect, isProcessingAtom, runCommandAtom } from "../../store/editor-atoms";
import { deletedChatAtom } from '../../store/chat-atoms'
import { preferencesAtom } from '../../store/preferences-atoms'

import path from "node:path";
import { proofAtom } from "../../store/editor-atoms";
import { ExerciseStatement } from "./ExerciseStatement";
import { ProofStep } from "./ProofStep";
import { TypewriterCommandLine } from "./typewriter/TypewriterCommandline";

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
        {proof?.steps.map((step, i) => <ProofStep step={step} idx={i} />)}
      </div>
    </div>
    <TypewriterCommandLine />
  </div>
}
