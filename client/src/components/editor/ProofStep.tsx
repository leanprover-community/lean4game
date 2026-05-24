import React from "react";
import { InteractiveGoalsWithHints } from "../../api/rpc_api";
import { Button } from "../button";
import { FontAwesomeIcon } from "@fortawesome/react-fontawesome";
import { faDeleteLeft } from "@fortawesome/free-solid-svg-icons";
import { useAtom } from "jotai";
import { proofAtom } from "../../store/editor-atoms";

export function ProofStep({step, idx}: {step:InteractiveGoalsWithHints, idx: number}) {
  const [proofState] = useAtom(proofAtom)

  return <div key={idx} >Step {idx} {step.command}
    <div className="command">
        <div className="command-text">{step.command}</div>
        <Button  className="undo-button btn btn-inverted" title={"Retry proof from here"}>
          <FontAwesomeIcon icon={faDeleteLeft} />&nbsp;{"Retry"}
        </Button>
      </div>
    <div>
      {proofState?.completed &&
        <div className="information ml1 message">
          <pre className="font-code pre-wrap">level completed! 🎉</pre>
        </div>}
    </div>
  </div>
}
