import { Atom, atom } from "jotai";
import { InventoryTile } from "../state/api";
import { levelIdAtom, worldIdAtom } from "./game-atoms";

/** Valid inventory tabs */
export enum InventoryTab {
  theorem = "theorem",
  tactic = "tactic",
  definition = "definition",
}

/** The user's inventory from local storage.
 *
 * TODO: currently this needs to be set in a `useEffect`
*/
export const userInventoryAtom = atom([] as string[])

/** Curently selected tab */
export const inventoryTabAtom = atom(InventoryTab.tactic)

/** Currently selected subtabs for all tabs. The active one should be
 * accessed through `inventorySubtabAtom` below.
 */
export const inventorySubtabAtoms: Record<InventoryTab, ReturnType<typeof atom<string>>> = {
  [InventoryTab.theorem]: atom(null as string | null),
  [InventoryTab.tactic]: atom(null as string | null),
  [InventoryTab.definition]: atom(null as string | null),
};

/** Change the subtab for theorems */
export const theoremSubtabAtom = atom(null, (get, set, val: string) => {
  set(inventorySubtabAtoms[InventoryTab.theorem], val)
})

/** Currently open doc entry */
export const selectedDocTileAtom = atom(null as InventoryTile | null)

/** Close the currently open doc entry */
export const closeDocAtom = atom(null, (get, set) => {
  set(selectedDocTileAtom, null)
})

/** The entire inventory
 * TODO: Currently set with a `useEffect`. Should probably be a query atom...
 */
export const inventoryTilesAtoms: Record<InventoryTab, ReturnType<typeof atom<InventoryTile[]>>> = {
  [InventoryTab.theorem]: atom([]),
  [InventoryTab.tactic]: atom([]),
  [InventoryTab.definition]: atom([]),
}

/** New items per tab */
export const inventoryTabNewTilesAtom: Atom<Record<InventoryTab, InventoryTile[]>> = atom( get => ({
  [InventoryTab.theorem]: get(inventoryTilesAtoms[InventoryTab.theorem]).filter(it => it.new),
  [InventoryTab.tactic]: get(inventoryTilesAtoms[InventoryTab.tactic]).filter(it => it.new),
  [InventoryTab.definition]: get(inventoryTilesAtoms[InventoryTab.definition]).filter(it => it.new),
}))

/** Recent items per tab */
export const inventoryTabRecentTilesAtom: Atom<Record<InventoryTab, InventoryTile[]>> = atom( get => {
  const worldId = get(worldIdAtom)
  const levelId = get(levelIdAtom)
  return {
    [InventoryTab.theorem]: get(inventoryTilesAtoms[InventoryTab.theorem]).filter(it => it.world == worldId && it.level == levelId - 1),
    [InventoryTab.tactic]: get(inventoryTilesAtoms[InventoryTab.tactic]).filter(it => it.world == worldId && it.level == levelId - 1),
    [InventoryTab.definition]: get(inventoryTilesAtoms[InventoryTab.definition]).filter(it => it.world == worldId && it.level == levelId - 1),
  }
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
  const tiles = get(inventoryTilesAtoms[tab])
  return [...new Set(tiles.map(item => item.category))]
})

/** Currently selected subtab */
export const inventorySubtabAtom = atom(
  get => {
    const tab = get(inventoryTabAtom)
    const options = get(inventorySubtabOptionsAtom)
    const subtab = get(inventorySubtabAtoms[tab])
    return subtab ?? options[0]
  },
  (get, set, val: string) => {
    const tab = get(inventoryTabAtom)
    set(inventorySubtabAtoms[tab], val)
  }
)

/** The currently visible inventory tiles */
export const currentInventoryTilesAtom = atom(get => {
  const tab = get(inventoryTabAtom)
  const subtab = get(inventorySubtabAtom)
  const userInventory = get(userInventoryAtom)
  return get(inventoryTilesAtoms[tab])
    .filter(it => !it.hidden && it.category == subtab)
    .map(tile => userInventory.includes(tile.name) ? {...tile, locked: false} : tile)
})
