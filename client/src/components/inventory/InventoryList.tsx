import React from "react"
import { selectDifficulty, selectInventory } from "../../state/progress"
import { InventoryOverview, InventoryTile, LevelInfo } from "../../state/api"
import { GameIdContext } from "../../app"
import { WorldLevelIdContext } from "../infoview/context"
import { useSelector } from "react-redux"
import { store } from "../../state/store"
import { InventoryItem } from "./InventoryItem"

export function InventoryList({items, docType, openDoc, tab=null, setTab=undefined, level=undefined, enableAll=false} :
  {
    items: InventoryTile[],
    docType: string,
    openDoc(props: {name: string, type: string}): void,
    tab?: any,
    setTab?: any,
    level?: LevelInfo|InventoryOverview,
    enableAll?: boolean,
  }) {
  // TODO: `level` is only used in the `useEffect` below to check if a new level has
  // been loaded. Is there a better way to observe this?

  const gameId = React.useContext(GameIdContext)
  const {worldId, levelId} = React.useContext(WorldLevelIdContext)

  const difficulty = useSelector(selectDifficulty(gameId))

  const categorySet = new Set<string>()
  for (let item of items) {
    categorySet.add(item.category)
  }
  const categories = Array.from(categorySet).sort()

  // Add inventory items from local store as unlocked.
  // Items are unlocked if they are in the local store, or if the server says they should be
  // given the dependency graph. (OR-connection) (TODO: maybe add different logic for different
  // modi)
  let inv: string[] = selectInventory(gameId)(store.getState())
  let modifiedItems : InventoryTile[] = items.map(tile => inv.includes(tile.name) ? {...tile, locked: false} : tile)

  // Item(s) proved in the preceeding level
  let recentItems = modifiedItems.filter(x => x.world == worldId && x.level == levelId - 1)

  return <>
    {categories.length > 1 &&
      <div className="tab-bar">
        {categories.map((cat) => {
          let hasNew = modifiedItems.filter(item => item.new && (cat == item.category)).length > 0
          return <div key={`category-${cat}`} className={`tab${cat == (tab ?? categories[0]) ? " active": ""}${hasNew ? ' new': ''}${recentItems.map(it => it.category).includes(cat) ? ' recent': ''}`}
            onClick={() => { setTab(cat) }}>{cat}</div>})}
      </div>}
    <div className="inventory-list">
      {[...modifiedItems].sort(
          // For lemas, sort entries `available > disabled > locked`
          // otherwise alphabetically
          (x, y) => +(docType === "Lemma") * (+x.locked - +y.locked || +x.disabled - +y.disabled) || x.displayName.localeCompare(y.displayName)
        ).filter(item => !item.hidden && ((tab ?? categories[0]) == item.category)).map((item, i) => {
            return <InventoryItem key={`${item.category}-${item.name}`}
              item={item}
              showDoc={() => {openDoc({name: item.name, type: docType})}}
              name={item.name} displayName={item.displayName} locked={difficulty > 0 ? item.locked : false}
              disabled={item.disabled}
              recent={recentItems.map(it => it.name).includes(item.name)}
              newly={item.new}
              isTheorem={docType === "Lemma"}
              enableAll={enableAll} />
        })
      }
    </div>
    </>
}
