import { type Atom, atom } from 'jotai'
import { atomEffect } from 'jotai-effect'
import { atomFamily } from 'jotai-family'
import { atomWithQuery } from 'jotai-tanstack-query'

import type { ApiDoc, ApiInventoryOverview, ApiInventoryTile } from '../api'
import { gameIdAtom, levelIdAtom, worldIdAtom } from '../state/location-atoms'
import { preferencesAtom } from '../state/preferences-atoms'
import { completedAtom, progressAtom } from '../state/progress-atoms'
import { levelInfoAtom } from '../state/query-atoms'
import { fetchJson, gameDataUrl } from '../utils/fetch'

/** Valid inventory tabs */
export const InventoryTab = {
  theorem: 'theorem',
  tactic: 'tactic',
  definition: 'definition',
} as const
export type InventoryTab = (typeof InventoryTab)[keyof typeof InventoryTab]

/** The inventory of the whole game, shown outside of levels */
export const inventoryOverviewAtom = atomWithQuery<ApiInventoryOverview>(
  get => {
    const gameId = get(gameIdAtom)
    return {
      queryKey: ['inventoryOverview', gameId],
      queryFn: () =>
        fetchJson<ApiInventoryOverview>(gameDataUrl(gameId!, 'inventory')),
      enabled: gameId !== undefined,
    }
  },
)

/** The documentation of a tactic, theorem or definition */
export const docAtomFamily = atomFamily(
  ([tab, name]: [InventoryTab, string]) =>
    atomWithQuery<ApiDoc>(get => {
      const gameId = get(gameIdAtom)
      return {
        queryKey: ['doc', gameId, tab, name],
        queryFn: () =>
          fetchJson<ApiDoc>(
            gameDataUrl(gameId!, `doc/${tab}/${encodeURIComponent(name)}`),
          ),
        enabled: gameId !== undefined,
      }
    }),
  (a, b) => a[0] === b[0] && a[1] === b[1],
)

/**
 * The user's unlocked inventory.
 * The setter adds the new constants to the existing inventory
 * ignoring duplicates.
 *  */
export const inventoryAtom = atom(
  get => {
    const progress = get(progressAtom)
    if (!progress) return null
    return progress.inventory
  },
  (get, set, val: string[]) => {
    const progress = get(progressAtom)
    if (!progress) return
    const newInventory = [...new Set([...progress.inventory, ...val])]
    set(progressAtom, { ...progress, inventory: newInventory })
  },
)

/** Curently selected tab */
export const inventoryTabAtom = atom<InventoryTab>(InventoryTab.tactic)

/** Currently selected subtabs for all tabs, `null` for the default. The active one
 * should be accessed through `inventorySubtabAtom` below.
 */
export const inventorySubtabAtoms = {
  [InventoryTab.theorem]: atom<string | null>(null),
  [InventoryTab.tactic]: atom<string | null>(null),
  [InventoryTab.definition]: atom<string | null>(null),
}

/** Change the subtab for theorems */
export const theoremSubtabAtom = atom(null, (_get, set, val: string) => {
  set(inventorySubtabAtoms[InventoryTab.theorem], val)
})

/** Currently open doc entry */
export const selectedDocTileAtom = atom<ApiInventoryTile | null>(null)

/** Close the currently open doc entry */
export const closeDocAtom = atom(null, (_get, set) => {
  set(selectedDocTileAtom, null)
})

/**
 * Whether the inventory of the current level is shown, otherwise the one of the
 * whole game. Level 0 is the introduction of a world.
 */
const inLevelAtom = atom(get => (get(levelIdAtom) ?? 0) > 0)

/** The data the inventory is built from, `undefined` while loading */
const inventoryDataAtom = atom(get =>
  get(inLevelAtom) ? get(levelInfoAtom).data : get(inventoryOverviewAtom).data,
)

/** The entire inventory per tab: of the current level, or of the whole game */
export const inventoryTilesAtom: Atom<
  Record<InventoryTab, ApiInventoryTile[]>
> = atom(get => {
  const data = get(inventoryDataAtom)
  return {
    [InventoryTab.theorem]: data?.theorems ?? [],
    [InventoryTab.tactic]: data?.tactics ?? [],
    [InventoryTab.definition]: data?.definitions ?? [],
  }
})

/** Apply `filter` to the tiles of each tab */
function filterTiles(
  tiles: Record<InventoryTab, ApiInventoryTile[]>,
  filter: (tile: ApiInventoryTile) => boolean,
): Record<InventoryTab, ApiInventoryTile[]> {
  return {
    [InventoryTab.theorem]: tiles[InventoryTab.theorem].filter(filter),
    [InventoryTab.tactic]: tiles[InventoryTab.tactic].filter(filter),
    [InventoryTab.definition]: tiles[InventoryTab.definition].filter(filter),
  }
}

/** New items per tab */
export const inventoryTabNewTilesAtom = atom(get =>
  filterTiles(get(inventoryTilesAtom), it => it.new),
)

/** Items introduced in the previous level, per tab */
export const inventoryTabRecentTilesAtom = atom(get => {
  const worldId = get(worldIdAtom)
  const levelId = get(levelIdAtom)
  return filterTiles(
    get(inventoryTilesAtom),
    it =>
      levelId !== undefined && it.world === worldId && it.level === levelId - 1,
  )
})

/** New items in the current tab */
export const inventoryCurrentTabNewTilesAtom = atom(get => {
  const tab = get(inventoryTabAtom)
  return get(inventoryTabNewTilesAtom)[tab]
})

/** Recent items in the current tab */
export const inventoryCurrentTabRecentTilesAtom = atom(get => {
  const tab = get(inventoryTabAtom)
  return get(inventoryTabRecentTilesAtom)[tab]
})

/** All subtabs of current tab */
export const inventorySubtabOptionsAtom = atom(get => {
  const tab = get(inventoryTabAtom)
  const tiles = get(inventoryTilesAtom)[tab]
  return [...new Set(tiles.map(item => item.category))]
})

/**
 * Currently selected subtab. Unless the player chose one, the theorem tab opens the
 * subtab the level asks for with `TheoremTab`, otherwise the first one.
 */
export const inventorySubtabAtom = atom(
  get => {
    const tab = get(inventoryTabAtom)
    const options = get(inventorySubtabOptionsAtom)
    const subtab = get(inventorySubtabAtoms[tab])
    const data = get(inventoryDataAtom)
    const theoremTab = tab === InventoryTab.theorem ? data?.theoremTab : null
    return subtab ?? theoremTab ?? options[0]
  },
  (get, set, val: string) => {
    const tab = get(inventoryTabAtom)
    set(inventorySubtabAtoms[tab], val)
  },
)

/** The currently visible inventory tiles, the ones in the user's inventory unlocked */
export const currentInventoryTilesAtom = atom(get => {
  const tab = get(inventoryTabAtom)
  const subtab = get(inventorySubtabAtom)
  const userInventory = get(inventoryAtom) ?? []
  const showLocked = get(preferencesAtom).showLockedInventory
  const tiles = get(inventoryTilesAtom)[tab]

  return tiles
    .map(tile =>
      userInventory.includes(tile.name) ? { ...tile, locked: false } : tile,
    )
    .filter(
      it => !it.hidden && it.category === subtab && (showLocked || !it.locked),
    )
})

/**
 * Completing a level unlocks its new items and its own theorem for good. This also
 * catches up when opening a level which was completed before this was stored.
 */
export const unlockLevelItemsEffect = atomEffect((get, set) => {
  const level = get(levelInfoAtom).data
  if (!level || !get(completedAtom)) return
  const unlocked = [
    ...[...level.tactics, ...level.theorems, ...level.definitions]
      .filter(tile => tile.new)
      .map(tile => tile.name),
    ...level.theorems
      .filter(tile => tile.name === level.statementName)
      .map(tile => tile.name),
  ]
  const inventory = get.peek(inventoryAtom) ?? []
  if (unlocked.some(name => !inventory.includes(name))) {
    set(inventoryAtom, unlocked)
  }
})
