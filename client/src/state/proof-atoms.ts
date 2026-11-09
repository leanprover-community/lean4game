import { atom } from 'jotai'
import { atomEffect } from 'jotai-effect'
import { atomWithQuery } from 'jotai-tanstack-query'

import type {
  ApiDiagnostic,
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

/** The proof of the current level as stored in local storage, one tactic per line */
export const codeAtom = atom(
  get => get(levelProgressAtom)?.code ?? '',
  (get, set, code: string) => {
    const levelProgress = get(levelProgressAtom)
    if (levelProgress == null) return
    set(levelProgressAtom, { ...levelProgress, code })
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

/** The non-empty lines of the code, which are sent to the server */
export const tacticsAtom = atom(get =>
  get(codeAtom)
    .split('\n')
    .map(line => line.trimEnd())
    .filter(line => line.trim().length > 0),
)

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
  const tactics = get(tacticsAtom)
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

/** The "unsolved goals" error, which is redundant as the goals are shown anyway */
export function isUnsolvedGoals(diagnostic: ApiDiagnostic) {
  return diagnostic.message.startsWith('unsolved goals')
}

/** The step has an error, apart from unsolved goals */
export function hasError(step: ApiProofStep | undefined) {
  return (
    step?.diagnostics.some(d => d.severity === 1 && !isUnsolvedGoals(d)) ??
    false
  )
}

/** The proof steps of the code, from the server's tactic texts */
function codeOfSteps(steps: ApiProofStep[]) {
  return steps
    .slice(1)
    .map(step => step.tactic)
    .join('\n')
}

/**
 * Appends the entered `text` to the proof. A failed last command is replaced, as it is
 * shown as "Failed command" which is removed on the next try. Returns whether the proof
 * changed, i.e. whether it is checked again.
 */
export const submitTacticAtom = atom(null, (get, set, text: string) => {
  const input = text.trimEnd()
  if (input.trim().length === 0) return false
  const before = get(tacticsAtom).join('\n')
  const steps = get(proofCheckAtom).data?.steps
  let code = get(codeAtom).trimEnd()
  if (steps && steps.length > 1 && hasError(steps.at(-1))) {
    code = codeOfSteps(steps.slice(0, -1))
  }
  set(codeAtom, code.length > 0 ? `${code}\n${input}` : input)
  const changed = get(tacticsAtom).join('\n') !== before
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
  set(codeAtom, codeOfSteps(steps.slice(0, i)))
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
    const before = get(tacticsAtom).join('\n')
    const code = codeOfSteps(steps.slice(0, i))
    set(codeAtom, code.length > 0 ? `${code}\n${input}` : input)
    const changed = get(tacticsAtom).join('\n') !== before
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
