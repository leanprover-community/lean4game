import { ContextInfo, InteractiveHypothesisBundle, CodeWithInfos, MVarId } from '@leanprover/infoview-api';

export interface GameHint {
  text: string;
  hidden: boolean;
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
