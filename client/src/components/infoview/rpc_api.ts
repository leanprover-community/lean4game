/**
 *  @fileOverview Defines the interface for the communication with the server.
 *
 * This file is based on `vscode-lean4/vscode-lean4/src/rpcApi.ts`
 */
import type { Range } from 'vscode-languageserver-protocol';
import type { ContextInfo, FVarId, CodeWithInfos, MVarId } from '@leanprover/infoview-api';
import { InteractiveDiagnostic, TermInfo } from '@leanprover/infoview/*';
import type { Diagnostic } from 'vscode-languageserver-protocol';

export interface InteractiveHypothesisBundle {
  /** The pretty names of the variables in the bundle. Anonymous names are rendered
   * as `"[anonymous]"` whereas inaccessible ones have a `✝` appended at the end.
   * Use `InteractiveHypothesisBundle_nonAnonymousNames` to filter anonymouse ones out. */
  names: string[];
  fvarIds?: FVarId[];
  type: CodeWithInfos;
  val?: CodeWithInfos;
  isInstance?: boolean;
  isType?: boolean;
  isInserted?: boolean;
  isRemoved?: boolean;
  isAssumption?: boolean;
}

export interface InteractiveGoalCore {
  hyps: InteractiveHypothesisBundle[];
  type: CodeWithInfos;
  ctx?: ContextInfo;
}

export interface InteractiveGoal extends InteractiveGoalCore {
  userName?: string;
  goalPrefix?: string;
  mvarId?: MVarId;
  isInserted?: boolean;
  isRemoved?: boolean;
}

export interface InteractiveGoals extends InteractiveGoalCore {
  goals: InteractiveGoals[];
}

export interface InteractiveTermGoal extends InteractiveGoalCore {
  range?: Range;
  term?: TermInfo;
}

export interface GameHint {
  text: string;
  hidden: boolean;
}

export interface InteractiveGoalWithHints {
  goal: InteractiveGoal;
  hints: GameHint[];
}

export interface InteractiveGoalsWithHints {
  goals: InteractiveGoalWithHints[];
  command: string;
  diags: InteractiveDiagnostic[];
}

/**
 * The proof state as it is received from the server.
 * Per proof step of the tactic proof, there is one `InteractiveGoalWithHints[]`.
 */
export interface ProofState {
  /** The proof steps. step 0 is the state at the beginning of the proof. step one
   * contains the goal after the first line has been evaluated.
   *
   * In particular `step[i]` is the proof step at the beginning of line `i` in vscode.
   */
  steps: InteractiveGoalsWithHints[];
  /** The remaining diagnostics that are not in the steps. Usually this should only
   * be the "unsolved goals" message, I believe.
   */
  diagnostics : InteractiveDiagnostic[];
  completed : Boolean;
  completedWithWarnings : Boolean;
}
