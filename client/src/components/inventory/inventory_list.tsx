import React from "react"
import { InventoryTile } from "../../store/api"
import { InventoryItem } from "./inventory_item"
import { currentInventoryTilesAtom, inventoryAtom, InventoryTab } from "../../store/inventory-atoms"
import { useAtom } from "jotai"
import { gameIdAtom, levelIdAtom, worldIdAtom } from "../../store/location-atoms"

export function InventoryList({tiles, docType, enableAll=false} : {
  tiles: InventoryTile[],
  docType: InventoryTab,
  enableAll?: boolean,
}) {
  const [currentTiles] = useAtom(currentInventoryTilesAtom)
  const [worldId] = useAtom(worldIdAtom)
  const [levelId] = useAtom(levelIdAtom)
  const [inventory] = useAtom(inventoryAtom)


  // Add inventory items from local store as unlocked.
  // Items are unlocked if they are in the local store, or if the server says they should be
  // given the dependency graph. (OR-connection) (TODO: maybe add different logic for different
  // modi)
  let modifiedItems : InventoryTile[] = tiles.map(tile => inventory?.includes(tile.name) ? {...tile, locked: false} : tile)

  // Item(s) proved in the preceeding level
  let recentItems = levelId ? modifiedItems.filter(x => x.world == worldId && x.level == levelId - 1) : []

  return <>
    <div className="inventory-list">

      {currentTiles.sort(
          // For theorems, sort entries `available > disabled > locked`
          // otherwise alphabetically
          (x, y) => +(docType === InventoryTab.theorem) * (+x.locked - +y.locked || +x.disabled - +y.disabled) || x.displayName.localeCompare(y.displayName)
        ).map((tile, i) => {
            return <InventoryItem key={`${tile.category}-${tile.name}`}
              tile={tile}
              recent={recentItems.map(it => it.name).includes(tile.name)}
              isTheorem={docType === InventoryTab.theorem}
              enableAll={enableAll} />
        })
      }
    </div>
    </>
}
