/* This file is based on `vscode-lean4/vscode-lean4/src/rpcApi.ts ` */

import { ContextInfo, FVarId, CodeWithInfos, MVarId } from '@leanprover/infoview-api';

export interface GameHint {
  text: string;
  hidden: boolean;
}

export interface InteractiveHypothesisBundle {
  /** The pretty names of the variables in the bundle. Anonymous names are rendered
   * as `"[anonymous]"` whereas inaccessible ones have a `✝` appended at the end.
   * Use `InteractiveHypothesisBundle_nonAnonymousNames` to filter anonymouse ones out. */
  names: string[];
  /** Present since server version 1.1.2. */
  fvarIds?: FVarId[];
  type: CodeWithInfos;
  val?: CodeWithInfos;
  isInstance?: boolean;
  isType?: boolean;
  isAssumption?: boolean;
  isInserted?: boolean;
  isRemoved?: boolean;
}

export interface InteractiveGoalCore {
  hyps: InteractiveHypothesisBundle[];
  type: CodeWithInfos;
  /** Present since server version 1.1.2. */
  ctx?: ContextInfo;
}

export interface InteractiveGoal extends InteractiveGoalCore {
  userName?: string;
  goalPrefix?: string;
  /** Present since server version 1.1.2. */
  mvarId?: MVarId;
  isInserted?: boolean;
  isRemoved?: boolean;
  hints: GameHint[];
}

export interface InteractiveGoals {
  goals: InteractiveGoal[];
}
