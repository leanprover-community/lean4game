import React from "react";
import { InteractiveGoalsWithHints } from "../../api/rpc_api";

export function ProofStep({step, idx}: {step:InteractiveGoalsWithHints, idx: number}) {
  return <div>Step {idx}</div>
}
