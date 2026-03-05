import { atom } from 'jotai'
import { atomWithLocation } from 'jotai-location'

const locationAtom = atomWithLocation()

export const navigateToLandingPageAtom = atom(null, (get, set) => {
  set(locationAtom, { hash: "" }, { replace: true })
})

/**
 * Splitting `#/g/test/TestGame/world/TestWorld/level/1` into
 * ["g", "test", "TestGame", "world", "TestWorld", "level", "1"]
 */
export const hashSegmentsAtom = atom((get) => {
  const { hash } = get(locationAtom)
  const clean = hash.replace(/^#\/*/, "")
  return clean.split("/").filter(Boolean)
})

export const gameIdAtom = atom((get) => {
  const segments = get(hashSegmentsAtom)
  if (segments.length < 3 || segments[0] !== "g") return null
  return segments.slice(0, 3).join("/")
}, (_get, set, gameId: string) => {
  set(locationAtom, { hash: `#/${gameId}` }, { replace: true })
})

export const worldIdAtom = atom((get) => {
  const segments = get(hashSegmentsAtom)
  if (segments.length < 5 || segments[3] !== "world") return null
  return segments[4]
}, (get, set, worldId: string) => {
  const gameId = get(gameIdAtom)
  set(locationAtom, { hash: `#/${gameId}/world/${worldId}` }, { replace: true })
})

export const levelIdAtom = atom((get) => {
  const segments = get(hashSegmentsAtom)
  if (segments.length < 7 || segments[5] !== "level") return null
  const value = Number(segments[6])
  return Number.isFinite(value) ? value : null
}, (get, set, levelId: number) => {
  const gameId = get(gameIdAtom)
  const worldId = get(worldIdAtom)
  set(locationAtom, { hash: `#/${gameId}/world/${worldId}/level/${Math.max(levelId, 0)}` }, { replace: true })}
)

export const navigateAcrossWorldsAtom = atom(null, (get, set, worldId: string, levelId: number) => {
  const gameId = get(gameIdAtom)
  set(locationAtom, { hash: `#/${gameId}/world/${worldId}/level/${Math.max(levelId, 0)}` }, { replace: true })
})
