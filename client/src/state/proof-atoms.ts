import { atom } from 'jotai'
import { atomEffect } from 'jotai-effect'
import { atomWithQuery } from 'jotai-tanstack-query'

import type {
  ApiProofCheckInput,
  ApiProofCheckResult,
  ApiProofStep,
} from '../api'
import i18n from '../i18n'
import { inventoryAtom } from '../Inventory/inventory-atoms'
import { HttpError, postJson, retryUnlessClientError } from '../utils/fetch'
import { gameIdAtom, levelIdAtom, worldIdAtom } from './location-atoms'
import {
  completedAtom,
  difficultyAtom,
  levelProgressAtom,
} from './progress-atoms'
import { levelInfoAtom } from './query-atoms'

/**
 * The steps of the proof of the current level as stored in local storage, which are sent
 * to the server. A step may span several lines, e.g. `have h : P := by\n  simp`.
 */
export const proofAtom = atom(
  get => get(levelProgressAtom)?.proof ?? [],
  (get, set, proof: string[]) => {
    const levelProgress = get(levelProgressAtom)
    if (levelProgress == null) return
    set(levelProgressAtom, { ...levelProgress, proof })
  },
)

/** The text in the input line of the typewriter */
export const typewriterInputAtom = atom('')

/** Incremented to focus the input line, e.g. after putting a command there to modify it */
export const typewriterFocusAtom = atom(0)

/** Puts `text` into the input line, ready to be modified */
export const editInTypewriterAtom = atom(null, (_get, set, text: string) => {
  set(typewriterInputAtom, text)
  set(typewriterFocusAtom, n => n + 1)
})

/** Keep track of all opened Lean instances to close them when
 * the page is closed
 */
const startedInstances = new Set<string>()

// stop Lean instance when the page is closed
window.addEventListener('pagehide', () => {
  for (const id of startedInstances) {
    navigator.sendBeacon(`/api/lean/instances/${id}/stop`)
  }
  startedInstances.clear()
})

/**
 * The Lean instance of the current game on the server. It is started once per game and
 * kept alive by `useLeanKeepalive`; refetch the query to start a new one.
 */
export const leanInstanceAtom = atomWithQuery<{ id: string }>(get => {
  const gameId = get(gameIdAtom)
  return {
    queryKey: ['leanInstance', gameId],
    queryFn: async () => {
      const instance = await postJson<{ id: string }>(
        `/api/lean/start/${gameId!.replace(/^g\//, '')}`,
      )
      startedInstances.add(instance.id)
      return instance
    },
    enabled: gameId !== undefined,
    staleTime: Infinity,
    gcTime: Infinity,
    retry: retryUnlessClientError,
  }
})

/**
 * The part of the inventory which can change the result of a check in this level. Other
 * items, like the ones unlocked by completing this level, must not cause a new check.
 */
const inventoryForCheckAtom = atom(get => {
  const inventory = get(inventoryAtom) ?? []
  const level = get(levelInfoAtom).data
  if (!level) return []
  return [...level.tactics, ...level.theorems, ...level.definitions]
    .filter(
      tile =>
        tile.locked &&
        tile.name !== level.statementName &&
        inventory.includes(tile.name),
    )
    .map(tile => tile.name)
})

/** The result of checking the current proof on the server */
export const proofCheckAtom = atomWithQuery<ApiProofCheckResult>(get => {
  const instanceId = get(leanInstanceAtom).data?.id
  const world = get(worldIdAtom)
  const level = get(levelIdAtom)
  const tactics = get(proofAtom)
  const inventory = get(inventoryAtom) ?? []
  const inventoryForCheck = get(inventoryForCheckAtom)
  const difficulty = get(difficultyAtom)
  return {
    queryKey: [
      'proofCheck',
      instanceId,
      world,
      level,
      tactics,
      inventoryForCheck,
      difficulty,
    ],
    queryFn: () =>
      postJson<ApiProofCheckResult>(`/api/lean/instances/${instanceId}/check`, {
        world: world!,
        level: level!,
        difficulty,
        inventory,
        tactics,
        hovers: true,
        language: i18n.language,
      } satisfies ApiProofCheckInput),
    enabled:
      instanceId !== undefined && world !== undefined && level !== undefined,
    // keep showing the previous proof of this level while the new one is checked,
    // but not the proof of another level
    placeholderData: (previousData, previousQuery) => {
      const [, prevInstance, prevWorld, prevLevel] =
        previousQuery?.queryKey ?? []
      return prevInstance === instanceId &&
        prevWorld === world &&
        prevLevel === level
        ? previousData
        : undefined
    },
    staleTime: Infinity,
    retry: false,
  }
})

/**
 * The step has an error. The server leaves out the "unsolved goals" of the whole proof,
 * but keeps others, e.g. of an empty `have : 0 = 1 := by`.
 */
export function hasError(step: ApiProofStep | undefined) {
  return step?.diagnostics.some(d => d.severity === 1) ?? false
}

/** The proof of the steps after the initial state, from the server's tactic texts */
function proofOfSteps(steps: ApiProofStep[]) {
  return steps.slice(1).map(step => step.tactic)
}

/** Sets the proof, returns whether it changed, i.e. whether it is checked again */
const setProofAtom = atom(null, (get, set, proof: string[]) => {
  const changed = JSON.stringify(proof) !== JSON.stringify(get(proofAtom))
  set(proofAtom, proof)
  return changed
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

/** The result of the proof check, only changes when a new result arrives */
const proofResultAtom = atom(get => get(proofCheckAtom).data)

/**
 * When a new result arrives after a submit: a command from the input line is cleared
 * if it worked, otherwise it stays to modify and try again; a step edited in place is
 * closed. A failed command is also put into an empty input line, e.g. after loading the
 * level.
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
  if (result.completed && !get.peek(completedAtom)) set(completedAtom, true)
})

/** Stops editing a step when going to another level */
export const resetEditingStepEffect = atomEffect((get, set) => {
  get(worldIdAtom)
  get(levelIdAtom)
  set(editingStepAtom, null)
})

/** The HTTP status of a failed proof check */
const checkStatusAtom = atom(get => {
  const { error } = get(proofCheckAtom)
  return error instanceof HttpError ? error.status : undefined
})

/** Starts a new Lean instance if it is gone, e.g. stopped after being idle */
export const restartInstanceEffect = atomEffect(get => {
  if (get(checkStatusAtom) === 404) void get.peek(leanInstanceAtom).refetch()
})
