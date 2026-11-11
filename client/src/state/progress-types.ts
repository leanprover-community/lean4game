export interface Selection {
  selectionStartLineNumber: number
  selectionStartColumn: number
  positionLineNumber: number
  positionColumn: number
}
export interface LevelProgress {
  /**
   * The steps of the proof. A step may span several lines, e.g. `have h : P := by\n  simp`.
   * Older versions stored the proof as `code`, one step per line, see `proofOfCode`.
   */
  proof: string[]
  selections: Selection[]
  completed: boolean
  help: number[] // The proof step of each revealed hidden hint, see `helpAtom`
}

export interface WorldProgress {
  [level: number]: LevelProgress
  readIntro: boolean
}

export interface GameProgress {
  inventory: string[]
  difficulty: number
  readIntro: boolean
  data: { [world: string]: WorldProgress }
  typewriterMode?: boolean
}

/**
 * Currently we have three difficulties:
 *
 *   | lock tactics | lock levels |
 * --|--------------|-------------|
 * 0 |      no      |      no     |
 * 1 |     yes      |      no     |
 * 2 |     yes      |     yes     |
 */
export const DEFAULT_DIFFICULTY = 2

/** The progress made on all lean4-games */
export interface Progress {
  games: { [game: string]: GameProgress }
}
