import { atom } from 'jotai'
import { atomWithLocation } from 'jotai-location'

const locationAtom = atomWithLocation()

export const navigateToLandingPageAtom = atom(null, (get, set) => {
  set(locationAtom, { hash: "", pathname: "" }, { replace: true })
})

/**
 * Splitting `#/g/test/TestGame/world/TestWorld/level/1` into
 * ["g", "test", "TestGame", "world", "TestWorld", "level", "1"]
 *
 * Deprecated: the urls of the form `/#/g/...` will be deprecated soon in favour normal Urls `/...`
 */
export const hashSegmentsAtom = atom((get) => {
  const { hash } = get(locationAtom)
  const clean = hash?.replace(/^#\/*/, "")
  return clean?.split("/").filter(Boolean) ?? []
})

/**
 * Splitting `/test/TestGame/TestWorld/1` into
 * ["test", "TestGame", "TestWorld", "1"]
 */
export const pathSegmentsAtom = atom((get) => {
  const { pathname } = get(locationAtom)
  return pathname?.split("/").filter(Boolean) ?? []
})

export const gameIdAtom = atom((get) => {
  const segments = get(pathSegmentsAtom).map(it => it.toLowerCase())
  if (segments.length >= 2) {
    return `g/${segments[0]}/${segments[1]}`
  }
  // for backwards compatibility:
  const hashSegments = get(hashSegmentsAtom).map(it => it.toLowerCase())
  if (hashSegments.length >= 3 && hashSegments[0] === "g") {
    return hashSegments.slice(0, 3).join("/")
  }
}, (get, set, gameId: string) => {
  const location = get(locationAtom)
  set(locationAtom, { ...location, hash: `#/${gameId}`, pathname: "" }, { replace: true })
})

export const worldIdAtom = atom((get) => {
  const segments = get(pathSegmentsAtom)
  if (segments.length >= 3) {
    return segments[2]
  }
  // for backwards compatibility:
  const hashSegments = get(hashSegmentsAtom)
  if (hashSegments.length >= 4 && hashSegments[3] === "world") {
    return hashSegments[4]
  }
}, (get, set, worldId: string) => {
  const gameId = get(gameIdAtom)
  const location = get(locationAtom)
  set(locationAtom, { ...location, hash: `#/${gameId}/world/${worldId}`, pathname: "" }, { replace: true })
})

export const levelIdAtom = atom((get) => {
  const segments = get(pathSegmentsAtom)
  if (segments.length >= 4) {
    const value = Number(segments[3])
    return Number.isFinite(value) ? value : undefined
  }
  // for backwards compatibility:
  const hashSegments = get(hashSegmentsAtom)
  if (hashSegments.length >= 6 && hashSegments[5] === "level") {
    const value = Number(hashSegments[6])
    return Number.isFinite(value) ? value : undefined
  }
}, (get, set, levelId: number) => {
  const gameId = get(gameIdAtom)
  const worldId = get(worldIdAtom)
  const location = get(locationAtom)
  set(locationAtom, { ...location, hash: `#/${gameId}/world/${worldId}/level/${Math.max(levelId, 0)}`, pathname: "" }, { replace: true })}
)

export const navigateAcrossWorldsAtom = atom(null, (get, set, worldId: string, levelId: number) => {
  const gameId = get(gameIdAtom)
  const location = get(locationAtom)
  set(locationAtom, { ...location, hash: `#/${gameId}/world/${worldId}/level/${Math.max(levelId, 0)}`, pathname: "" }, { replace: true })
})

export const redirectAtom = atom(null, (get, set, hash: string) => {
  const location = get(locationAtom)
  set(locationAtom, { ...location, hash: hash, pathname: "" }, { replace: true })
})
