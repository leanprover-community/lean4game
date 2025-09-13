import React from "react"
import { selectInventory } from "../../state/progress"
import { InventoryTile } from "../../state/api"
import { GameIdContext } from "../../app"
import { WorldLevelIdContext } from "../infoview/context"
import { store } from "../../state/store"
import { InventoryItem } from "./inventory_item"
import { currentInventoryTilesAtom, InventoryTab, inventoryTabAtom } from "../../store/inventory-atoms"
import { useAtom } from "jotai"
import { useSelector } from "react-redux"

export function InventoryList({tiles, docType, enableAll=false} : {
  tiles: InventoryTile[],
  docType: InventoryTab,
  enableAll?: boolean,
}) {
  const [currentTiles] = useAtom(currentInventoryTilesAtom)
  const gameId = React.useContext(GameIdContext)
  const {worldId, levelId} = React.useContext(WorldLevelIdContext)

  // Add inventory items from local store as unlocked.
  // Items are unlocked if they are in the local store, or if the server says they should be
  // given the dependency graph. (OR-connection) (TODO: maybe add different logic for different
  // modi)
  let inv: string[] = useSelector(selectInventory(gameId))
  let modifiedItems : InventoryTile[] = tiles.map(tile => inv.includes(tile.name) ? {...tile, locked: false} : tile)

  // Item(s) proved in the preceeding level
  let recentItems = modifiedItems.filter(x => x.world == worldId && x.level == levelId - 1)

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
