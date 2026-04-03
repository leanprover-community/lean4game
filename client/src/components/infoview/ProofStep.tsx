import React from "react";
import { InteractiveGoalsWithHints } from "./types";

export function ProofStep({step, idx}: {step:InteractiveGoalsWithHints, idx: number}) {
  return <div>Step {idx}</div>
}
