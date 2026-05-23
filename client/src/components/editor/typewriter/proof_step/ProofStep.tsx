import React from "react";
import { editor } from 'monaco-editor'
import { InteractiveGoalsWithHints } from "../../../../api/rpc_api";
import { useAtom } from "jotai";
import { helpAtom, selectedStepAtom } from "../../../../store/chat-atoms";
import { twMerge } from "tailwind-merge";
import { Command } from "./Command";
import { proofAtom } from "../../../../store/editor-atoms";
import { Errors } from "../../messages/Error";
import { mobileAtom } from "../../../../store/preferences-atoms";
import { gameInfoAtom, levelInfoAtom } from "../../../../store/query-atoms";
import { useGameTranslation } from "../../../../utils/translation";
import { filterHints, Hint, Hints } from "../../../hints";
import { i } from "@tanstack/query-core/build/legacy/hydration-BlEVG2Lp";
import { GoalsTabs } from "./GoalsTab";

export function ProofStep({step, idx}: {step:InteractiveGoalsWithHints, idx: number}) {
  const {t : gT} = useGameTranslation()
  const [selectedStep, setSelectedStep] = useAtom(selectedStepAtom)
  const [proof] = useAtom(proofAtom)
  const [help] = useAtom(helpAtom)
  const [mobile] = useAtom(mobileAtom)
  const [{ data: gameInfo }] = useAtom(gameInfoAtom)
  const [{ data: levelInfo }] = useAtom(levelInfoAtom)
  let introText: Array<string> = gT(levelInfo?.introduction ?? "").split(/\n(\s*\n)+/)

  function toggleSelectStep(line: number) {
    if (mobile) {return}
    setSelectedStep(selectedStep != line ? line : undefined)
  }

  // TODO: this should be an atom
  let filteredHints = proof ? filterHints(step.goals[0]?.hints, proof.steps[idx-1]?.goals[0]?.hints) : []

  if (!proof) return

  return (
    <div key={`proof-step-${idx}`} className={twMerge("step",  `step-${idx}`, (selectedStep == idx && ' selected'))}>
      <Command proof={proof} i={idx} />
      <Errors errors={step.diags} typewriterMode={true} />
      {mobile && idx == 0 && gameInfo?.introduction &&
        introText?.filter(it => it.trim()).map(((it, i) =>
          // Show the level's intro text as hints, too
          <Hint key={`intro-p-${i}`}
            hint={{text: it, hidden: false, rawText: it, varNames: []}} step={0} selected={selectedStep} toggleSelection={toggleSelectStep(0)} />
        ))
      }
      {mobile &&
        <Hints key={`hints-${idx}`}
          hints={filteredHints} showHidden={help.has(idx)} step={idx}
          selected={selectedStep} toggleSelection={toggleSelectStep(idx)}/>
      }
      <GoalsTabs
        proofStep={step}
        last={false} // FIXME
      // last={idx == proof.steps.length - (lastStepErrors ? 2 : 1)} onClick={toggleSelectStep(idx)}
      // onGoalChange={idx == proof.steps.length - 1 - withErr ? (n) => setDisableInput(n > 0) : (n) => {}}
      />
    </div>
  )
}


{/*


  {!(isLastStepWithErrors(proof, i)) &&
    <GoalsTabs proofStep={step} last={i == proof?.steps.length - (lastStepHasErrors(proof) ? 2 : 1)} onClick={toggleSelectStep(i)} onGoalChange={i == proof?.steps.length - (lastStepHasErrors(proof) ? 2 : 1) ? (n) => setDisableInput(n > 0) : (n) => {}}/>
  }
  {mobile && i == proof?.steps.length - 1 &&
    <MoreHelpButton selected={null} />
  }

  Show a message that there are no goals left
  {!step.goals.length && (
    <div className="message information">
      {proof?.completed ?
        <p>Level completed! 🎉</p> :
        <p>
          <b>no goals left</b><br />
          <i>This probably means you solved the level with warnings or Lean encountered a parsing error.</i>
        </p>
      }
    </div>
  )}
</div>  */}
