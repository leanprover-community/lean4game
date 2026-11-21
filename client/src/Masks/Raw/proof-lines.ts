import type { ApiProofStep } from '../../api'

/**
 * The lines of the proof which Lean numbers, as indices of the lines of `text`: Lean gets
 * the proof without empty lines, see `proofOfCode`
 */
export function proofLines(text: string) {
  return text
    .split('\n')
    .flatMap((line, i) => (line.trim().length > 0 ? [i] : []))
}

/** The first proof line of each step's tactic, the initial state has none */
export function stepStarts(steps: ApiProofStep[]) {
  const starts: (number | undefined)[] = []
  let next = 0
  for (const step of steps) {
    if (step.tactic.length === 0) {
      starts.push(undefined)
      continue
    }
    starts.push(next)
    next += step.tactic.split('\n').length
  }
  return starts
}

/**
 * The index of the step at the 0-based line `textLine` of `text`: the step whose tactic
 * is on the line, or on the last line with a tactic above, else the initial state, e.g.
 * for `-1`
 */
export function stepAtLine(
  steps: ApiProofStep[],
  text: string,
  textLine: number,
) {
  // the proof line at or above the text line
  const proofLine = proofLines(text).filter(i => i <= textLine).length - 1
  let index = 0
  stepStarts(steps).forEach((start, i) => {
    if (start !== undefined && start <= proofLine) index = i
  })
  return index
}
