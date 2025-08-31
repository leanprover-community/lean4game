import React from "react"
import { selectDifficulty, selectInventory } from "../../state/progress"
import { InventoryOverview, InventoryTile, LevelInfo } from "../../state/api"
import { GameIdContext } from "../../app"
import { WorldLevelIdContext } from "../infoview/context"
import { useSelector } from "react-redux"
import { store } from "../../state/store"
import { InventoryItem } from "./InventoryItem"
import { currentInventoryTilesAtom, inventoryTabAtom } from "../../store/inventory-atoms"
import { useAtom } from "jotai"

export function InventoryList({tiles, docType, enableAll=false} : {
  tiles: InventoryTile[],
  docType: string,
  enableAll?: boolean,
}) {

    // TODO: `level` is only used in the `useEffect` below to check if a new level has
  // been loaded. Is there a better way to observe this?

  const [currentTiles] = useAtom(currentInventoryTilesAtom)

  const gameId = React.useContext(GameIdContext)
  const {worldId, levelId} = React.useContext(WorldLevelIdContext)

  const difficulty = useSelector(selectDifficulty(gameId))

  const categorySet = new Set<string>()
  for (let tile of tiles) {
    categorySet.add(tile.category)
  }
  const categories = Array.from(categorySet).sort()

  // Add inventory items from local store as unlocked.
  // Items are unlocked if they are in the local store, or if the server says they should be
  // given the dependency graph. (OR-connection) (TODO: maybe add different logic for different
  // modi)
  let inv: string[] = selectInventory(gameId)(store.getState())
  let modifiedItems : InventoryTile[] = tiles.map(tile => inv.includes(tile.name) ? {...tile, locked: false} : tile)

  // Item(s) proved in the preceeding level
  let recentItems = modifiedItems.filter(x => x.world == worldId && x.level == levelId - 1)

  return <>
    <div className="inventory-list">

      {currentTiles.sort(
          // For lemas, sort entries `available > disabled > locked`
          // otherwise alphabetically
          (x, y) => +(docType === "Lemma") * (+x.locked - +y.locked || +x.disabled - +y.disabled) || x.displayName.localeCompare(y.displayName)
        ).map((tile, i) => {
            return <InventoryItem key={`${tile.category}-${tile.name}`}
              tile={tile}
              recent={recentItems.map(it => it.name).includes(tile.name)}
              isTheorem={docType === "Lemma"}
              enableAll={enableAll} />
        })
      }
    </div>
    </>
}
