import { atom } from 'jotai'
import { atomEffect } from 'jotai-effect'
import { atomWithLocation } from 'jotai-location'

import { gameInfoAtomFamily } from './game-info-atoms'

/** The current URL, kept in sync with the browser history */
export const locationAtom = atomWithLocation()

export const navigateToLandingPageAtom = atom(null, (_, set) => {
  set(locationAtom, { hash: '', pathname: '' }, { replace: true })
})

/**
 * Splitting `#/g/test/TestGame/world/TestWorld/level/1` into
 * ["g", "test", "TestGame", "world", "TestWorld", "level", "1"]
 *
 * Deprecated: the urls of the form `/#/g/...` will be deprecated soon in favour normal Urls `/...`
 */
const hashSegmentsAtom = atom(get => {
  const { hash } = get(locationAtom)
  const clean = hash?.replace(/^#\/*/, '')
  return clean?.split('/').filter(Boolean) ?? []
})

/**
 * Splitting `/test/TestGame/TestWorld/1` into
 * ["test", "TestGame", "TestWorld", "1"]
 */
const pathSegmentsAtom = atom(get => {
  const { pathname } = get(locationAtom)
  return pathname?.split('/').filter(Boolean) ?? []
})

/** The pages which are not part of a game */
const PAGES = ['impressum', 'privacy', 'preferences'] as const

/**
 * The page the URL points to. Game, world and level are lowercase, as they are
 * case-insensitive in the URL: `/g/owner/repo`, `/g/owner/repo/world`,
 * `/g/owner/repo/world/level` with levels numbered from 1. Games are under `/g/`, so
 * that they never collide with the other pages or the server's paths.
 */
export type Route =
  | { page: 'landing' }
  | { page: (typeof PAGES)[number] }
  | { page: 'game'; gameId: string }
  | { page: 'world'; gameId: string; world: string }
  | { page: 'level'; gameId: string; world: string; levelId: number }
  | { page: 'notFound' }

/** `segment` decoded and lowercase */
function lowercaseSegment(segment: string) {
  try {
    return decodeURIComponent(segment).toLowerCase()
  } catch {
    // malformed `%` escape
    return segment.toLowerCase()
  }
}

/** The game, world and level of `[owner, repo, world?, level?]` */
function gameRoute(segments: string[], levelPattern: RegExp): Route {
  const [owner, repo] = segments
  const world = segments.at(2)
  const level = segments.at(3)
  const gameId = `g/${lowercaseSegment(owner)}/${lowercaseSegment(repo)}`
  if (world === undefined) return { page: 'game', gameId }
  if (level === undefined)
    return { page: 'world', gameId, world: lowercaseSegment(world) }
  if (!levelPattern.test(level)) return { page: 'notFound' }
  const levelId = Number(level)
  // old URLs use level 0 for the introduction of the world
  if (levelId === 0)
    return { page: 'world', gameId, world: lowercaseSegment(world) }
  return { page: 'level', gameId, world: lowercaseSegment(world), levelId }
}

/** The URL parsed, see `Route` */
export const routeAtom = atom<Route>(get => {
  const segments = get(pathSegmentsAtom)
  if (segments.length === 0) {
    // for backwards compatibility: `#/g/owner/repo/world/world/level/level`
    const [g, owner, repo, w, world, l, level] = get(hashSegmentsAtom)
    if (g === 'g' && owner && repo) {
      const parts = [owner, repo]
      if (w === 'world' && world) {
        parts.push(world)
        if (l === 'level' && level) parts.push(level)
      }
      return gameRoute(parts, /^\d+$/)
    }
    return { page: 'landing' }
  }
  if (segments.length === 1) {
    const page = PAGES.find(p => p === segments[0])
    return page ? { page } : { page: 'notFound' }
  }
  if (segments[0] === 'g' && segments.length >= 3 && segments.length <= 5)
    return gameRoute(segments.slice(1), /^[1-9]\d*$/)
  return { page: 'notFound' }
})

/** Whether `route` is one of the pages of the menu, e.g. the preferences */
export function isMenuPage(route: Route) {
  return PAGES.some(p => p === route.page)
}

/**
 * The URL path of the game `gameId`, e.g. `g/owner/repo`, or of one of its worlds or
 * levels. Lowercase, as the URL is case-insensitive.
 */
export function gamePath(gameId: string, worldId?: string, levelId?: number) {
  let path = `/${gameId}`
  if (worldId !== undefined) path += `/${encodeURIComponent(worldId)}`
  if (levelId !== undefined) path += `/${levelId}`
  return path.toLowerCase()
}

/**
 * Replaces the URL of a game page by its canonical form: lowercase, as game and world
 * are case-insensitive, e.g. `/g/Owner/Repo/World/1` → `/g/owner/repo/world/1`, and old
 * URLs `/#/g/owner/repo/world/World/level/1` by the new ones.
 */
export const canonicalGamePathEffect = atomEffect((get, set) => {
  const location = get(locationAtom)
  const route = get(routeAtom)
  const canonical =
    route.page === 'game'
      ? gamePath(route.gameId)
      : route.page === 'world'
        ? gamePath(route.gameId, route.world)
        : route.page === 'level'
          ? gamePath(route.gameId, route.world, route.levelId)
          : undefined
  if (canonical === undefined) return
  if (location.pathname === canonical && !location.hash) return
  set(locationAtom, prev => ({ ...prev, pathname: canonical, hash: '' }), {
    replace: true,
  })
})

/** The game in the URL, e.g. `g/owner/repo`, lowercase */
export const gameIdAtom = atom(
  get => {
    const route = get(routeAtom)
    return 'gameId' in route ? route.gameId : undefined
  },
  (get, set, gameId: string) => {
    const location = get(locationAtom)
    set(
      locationAtom,
      { ...location, hash: '', pathname: gamePath(gameId) },
      { replace: true },
    )
  },
)

/**
 * The ID of the world in the URL, as in the game's `game.json`. The world in the URL is
 * case-insensitive. `undefined` while the game is loading or if it has no such world.
 */
export const worldIdAtom = atom(
  get => {
    const route = get(routeAtom)
    if (!('world' in route)) return undefined
    const worlds = get(gameInfoAtomFamily(route.gameId)).data?.worlds?.nodes
    return Object.keys(worlds ?? {}).find(
      id => id.toLowerCase() === route.world,
    )
  },
  (get, set, worldId: string) => {
    const gameId = get(gameIdAtom)
    if (gameId === undefined) return
    const location = get(locationAtom)
    set(
      locationAtom,
      { ...location, hash: '', pathname: gamePath(gameId, worldId) },
      { replace: true },
    )
  },
)

/** The level in the URL, from 1 */
export const levelIdAtom = atom(
  get => {
    const route = get(routeAtom)
    return 'levelId' in route ? route.levelId : undefined
  },
  (get, set, levelId: number) => {
    const gameId = get(gameIdAtom)
    const worldId = get(worldIdAtom)
    if (gameId === undefined || worldId === undefined) return
    set(navigateAcrossWorldsAtom, worldId, levelId)
  },
)

export const navigateAcrossWorldsAtom = atom(
  null,
  (get, set, worldId: string, levelId: number) => {
    const gameId = get(gameIdAtom)
    if (gameId === undefined) return
    const location = get(locationAtom)
    // level 0 is the world's introduction
    const pathname =
      levelId > 0
        ? gamePath(gameId, worldId, levelId)
        : gamePath(gameId, worldId)
    set(locationAtom, { ...location, hash: '', pathname }, { replace: true })
  },
)

/** Go to `pathname`, e.g. `/g/owner/repo` */
export const redirectAtom = atom(null, (get, set, pathname: string) => {
  const location = get(locationAtom)
  set(locationAtom, { ...location, hash: '', pathname }, { replace: true })
})
