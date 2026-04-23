export interface GameHint {
  text: string;
  hidden: boolean;
  rawText: string;
  varNames: string[][]; // in Lean: `Array (Name × Name)`
}
