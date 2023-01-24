import { InteractiveGoals, InteractiveGoal } from '@leanprover/infoview-api';

export interface GameHint {
  text: string;
  hidden: boolean;
}

export interface GameInteractiveGoal {
  goal: InteractiveGoal;
  hints: GameHint[];
}

export interface GameInteractiveGoals {
  goals: GameInteractiveGoal[];
}
