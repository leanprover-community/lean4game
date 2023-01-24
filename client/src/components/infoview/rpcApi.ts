import { InteractiveGoals, InteractiveGoal } from '@leanprover/infoview-api';

export interface GameMessage {
  message: string;
  spoiler: boolean;
}

export interface GameInteractiveGoal {
  goal: InteractiveGoal;
  messages: GameMessage[];
}

export interface GameInteractiveGoals {
  goals: GameInteractiveGoal[];
}
