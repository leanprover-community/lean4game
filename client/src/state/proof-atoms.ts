import { atom } from 'jotai'
import { atomEffect } from 'jotai-effect'
import { atomWithQuery } from 'jotai-tanstack-query'

import type {
  ApiLeanInstance,
  ApiLeanPhase,
  ApiPreloadInput,
  ApiProofCheckInput,
  ApiProofCheckResult,
  ApiProofStep,
} from '../api'
import i18n from '../i18n'
import { inventoryAtom } from '../Inventory/inventory-atoms'
import {
  fetchJson,
  HttpError,
  postJson,
  retryUnlessClientError,
} from '../utils/fetch'
import {
  gameIdAtom,
  levelIdAtom,
  routeAtom,
  worldIdAtom,
} from './location-atoms'
import {
  completedAtom,
  difficultyAtom,
  levelProgressAtom,
} from './progress-atoms'
import { gameInfoAtom, levelInfoAtom } from './query-atoms'

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

/** The game whose Lean instance is needed, see `requestLeanEffect` */
const leanGameAtom = atom<string | undefined>(undefined)

/**
 * Starts the Lean instance of the current game. Used on the pages of a world and a level,
 * not on the game's start page, see `leanInstanceAtom`.
 */
export const requestLeanEffect = atomEffect((get, set) => {
  const gameId = get(gameIdAtom)
  if (gameId !== undefined) set(leanGameAtom, gameId)
})

/**
 * The Lean instance of the current game on the server. It is started once per game, by
 * `requestLeanEffect`, and kept alive by `useLeanKeepalive` on all pages of the game;
 * refetch the query to start a new one.
 */
export const leanInstanceAtom = atomWithQuery<{ id: string }>(get => {
  const gameId = get(gameIdAtom)
  const requested = gameId !== undefined && get(leanGameAtom) === gameId
  return {
    queryKey: ['leanInstance', gameId],
    queryFn: async () => {
      const instance = await postJson<{ id: string }>(
        `/api/lean/start/${gameId!.replace(/^g\//, '')}`,
      )
      startedInstances.add(instance.id)
      return instance
    },
    enabled: requested,
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
export function proofOfSteps(steps: ApiProofStep[]) {
  return steps.slice(1).map(step => step.tactic)
}

/** Sets the proof, returns whether it changed, i.e. whether it is checked again */
export const setProofAtom = atom(null, (get, set, proof: string[]) => {
  const changed = JSON.stringify(proof) !== JSON.stringify(get(proofAtom))
  set(proofAtom, proof)
  return changed
})

/**
 * The Lean instance as the server reports it, polled while waiting for the first result
 * of a level, which can take long when the imports are loaded, e.g. all of Mathlib.
 */
const leanInstanceStateAtom = atomWithQuery<ApiLeanInstance>(get => {
  const instanceId = get(leanInstanceAtom).data?.id
  const check = get(proofCheckAtom)
  const waiting = check.isFetching && check.data === undefined
  return {
    queryKey: ['leanInstanceState', instanceId],
    queryFn: () =>
      fetchJson<ApiLeanInstance>(`/api/lean/instances/${instanceId}`),
    enabled: instanceId !== undefined && waiting,
    refetchInterval: 1000,
    retry: false,
  }
})

/**
 * What the Lean instance is doing while waiting for the first result of a level. An `idle`
 * instance is about to check: the request is on its way.
 */
export const leanPhaseAtom = atom<Exclude<ApiLeanPhase, 'idle'>>(get => {
  if (get(leanInstanceAtom).isPending) return 'starting'
  const phase = get(leanInstanceStateAtom).data?.phase ?? 'starting'
  return phase === 'idle' ? 'checking' : phase
})

/** The result of the proof check, only changes when a new result arrives */
export const proofResultAtom = atom(get => get(proofCheckAtom).data)

/** Marks the level as completed when a result says so */
export const levelCompletedEffect = atomEffect((get, set) => {
  const result = get(proofResultAtom)
  if (result?.completed && !get.peek(completedAtom)) set(completedAtom, true)
})

/** The levels already preloaded, as `instance/world/level` */
const preloadedLevels = new Set<string>()

/**
 * Lets the Lean instance load the imports of a level in the background, e.g. all of
 * Mathlib, so that it is ready when the player opens it.
 */
function preloadLevel(instanceId: string, world: string, level: number) {
  const key = `${instanceId}/${world}/${level}`
  if (preloadedLevels.has(key)) return
  preloadedLevels.add(key)
  postJson(`/api/lean/instances/${instanceId}/preload`, {
    world,
    level,
  } satisfies ApiPreloadInput).catch(() => preloadedLevels.delete(key))
}

/** On the introduction of a world, but not its conclusion, preloads its first level */
export const preloadFirstLevelEffect = atomEffect(get => {
  if (get(routeAtom).page !== 'world') return
  const instanceId = get(leanInstanceAtom).data?.id
  const world = get(worldIdAtom)
  if (instanceId === undefined || world === undefined) return
  preloadLevel(instanceId, world, 1)
})

/** Once the current level is completed, preloads the next level of the world */
export const preloadNextLevelEffect = atomEffect(get => {
  const instanceId = get(leanInstanceAtom).data?.id
  const world = get(worldIdAtom)
  const level = get(levelIdAtom)
  const worldSize = world && get(gameInfoAtom).data?.worldSize?.[world]
  if (!get(completedAtom)) return
  if (instanceId === undefined || world === undefined || level === undefined)
    return
  if (!worldSize || level >= worldSize) return
  preloadLevel(instanceId, world, level + 1)
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
