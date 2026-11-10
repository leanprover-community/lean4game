import { atom } from 'jotai'
import { atomEffect } from 'jotai-effect'

import { levelIdAtom, worldIdAtom } from '../../state/location-atoms'
import {
  hasError,
  proofAtom,
  proofCheckAtom,
  proofOfSteps,
  proofResultAtom,
  setProofAtom,
} from '../../state/proof-atoms'

/** The text in the input line of the typewriter */
export const typewriterInputAtom = atom('')

/** Incremented to focus the input line, e.g. after putting a command there to modify it */
export const typewriterFocusAtom = atom(0)

/** Puts `text` into the input line, ready to be modified */
export const editInTypewriterAtom = atom(null, (_get, set, text: string) => {
  set(typewriterInputAtom, text)
  set(typewriterFocusAtom, n => n + 1)
})

/**
 * Appends the entered `text` to the proof. A failed last command is replaced, as it is
 * shown as "Failed command" which is removed on the next try. Returns whether the proof
 * changed, i.e. whether it is checked again.
 */
export const submitTacticAtom = atom(null, (get, set, text: string) => {
  const input = text.trimEnd()
  if (input.trim().length === 0) return false
  const steps = get(proofCheckAtom).data?.steps
  let proof = get(proofAtom)
  if (steps && steps.length > 1 && hasError(steps.at(-1))) {
    proof = proofOfSteps(steps.slice(0, -1))
  }
  const changed = set(setProofAtom, [...proof, input])
  if (changed) set(submittedFromAtom, 'typewriter')
  return changed
})

/**
 * Deletes the proof from step `i` on, i.e. keeps the first `i - 1` tactics, and puts the
 * command of step `i` into the input line to modify it
 */
export const retryFromStepAtom = atom(null, (get, set, i: number) => {
  const steps = get(proofCheckAtom).data?.steps
  if (!steps) return
  set(proofAtom, proofOfSteps(steps.slice(0, i)))
  set(editInTypewriterAtom, steps[i]?.tactic ?? '')
})

/** The step whose command is edited in place, see `replaceStepAtom` */
export const editingStepAtom = atom<number | null>(null)

/**
 * Replaces the command of step `i` by `text` and deletes the proof after it. Returns
 * whether the proof changed, i.e. whether it is checked again.
 */
export const replaceStepAtom = atom(
  null,
  (get, set, i: number, text: string) => {
    const steps = get(proofCheckAtom).data?.steps
    const input = text.trimEnd()
    if (!steps || input.trim().length === 0) return false
    const changed = set(setProofAtom, [
      ...proofOfSteps(steps.slice(0, i)),
      input,
    ])
    if (changed) set(submittedFromAtom, 'step')
    return changed
  },
)

/**
 * Where the command which is being checked was entered: in the input line at the
 * bottom, or in place of an earlier step. See `proofResultEffect`.
 */
const submittedFromAtom = atom<'typewriter' | 'step' | null>(null)

/**
 * When a new result arrives after a submit: a command from the input line is cleared
 * if it worked, otherwise it stays to modify and try again; a step edited in place is
 * closed. A failed command is also put into an empty input line, e.g. after loading the
 * level. See `levelCompletedEffect` for the completion.
 */
export const proofResultEffect = atomEffect((get, set) => {
  const result = get(proofResultAtom)
  if (!result) return
  const last = result.steps.at(-1)
  const failed = result.steps.length > 1 && hasError(last)
  const submittedFrom = get.peek(submittedFromAtom)
  set(submittedFromAtom, null)
  if (submittedFrom === 'step') set(editingStepAtom, null)
  if (submittedFrom === 'typewriter') {
    set(editInTypewriterAtom, failed ? last!.tactic : '')
  } else if (failed && !get.peek(typewriterInputAtom)) {
    set(editInTypewriterAtom, last!.tactic)
  }
})

/** Stops editing a step when going to another level */
export const resetEditingStepEffect = atomEffect((get, set) => {
  get(worldIdAtom)
  get(levelIdAtom)
  set(editingStepAtom, null)
})
