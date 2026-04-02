export interface GameHint {
  text: string;
  hidden: boolean;
  rawText: string;
  varNames: string[][]; // in Lean: `Array (Name × Name)`
}

export interface InteractiveGoalWithHints {
  // goal: InteractiveGoal; // FIXME
  hints: GameHint[];
}

export interface InteractiveGoalsWithHints {
  goals: InteractiveGoalWithHints[];
  command: string;
  // diags: InteractiveDiagnostic[]; // FIXME
}
