import React from "react"
import { useTranslation } from "react-i18next"
import { inventoryCurrentTabNewTilesAtom, inventorySubtabAtom, inventorySubtabOptionsAtom, InventoryTab, inventoryTabAtom, inventoryTabNewTilesAtom } from "../../store/inventory-atoms"
import { useAtom } from "jotai"

function TabTitle(type: InventoryTab): string {
  switch(type) {
    case InventoryTab.theorem: return "Theorems"
    case InventoryTab.tactic: return "Tactics"
    case InventoryTab.definition: return "Definitions"
    default:
      const _exhaustive: never = type
  }
}

/** The major tab bar: choose between theorems, tactics, or definitions */
export function InventoryTabBar() {
  const { t } = useTranslation()
  const [tab, setTab] = useAtom(inventoryTabAtom)
  const [newTiles] = useAtom(inventoryTabNewTilesAtom)
  return (
    <div className="tab-bar major">
      { Object.values(InventoryTab).map(type => (
        <div
          key={type}
          className={`tab${(tab == type) ? " active": ""}${newTiles[type].length > 0 ? " new" : ""}`}
          onClick={() => {setTab(type)}}
        >
          {t(TabTitle(type))}
        </div>
      ))}
    </div>
  )
}

export function InventorySubTabBar() {
  const [tab] = useAtom(inventoryTabAtom)
  const [subtab, setSubtab] = useAtom(inventorySubtabAtom)
  const [newTiles] = useAtom(inventoryCurrentTabNewTilesAtom)
  const [options] = useAtom(inventorySubtabOptionsAtom)

  if (options.size < 2) return null

  function hasNew(cat: string) {
    return newTiles.filter(it => it.category == cat).length > 0
  }

  return (
    <div className="tab-bar">
      {[...options].map((cat) => {
        // let hasNew = modifiedItems.filter(item => item.new && (cat == item.category)).length > 0
        // return <div key={`category-${cat}`} className={`tab${cat == (tab ?? categories[0]) ? " active": ""}${hasNew ? ' new': ''}${recentItems.map(it => it.category).includes(cat) ? ' recent': ''}`}
        //   onClick={() => { setSubtab(cat) }}>{cat}</div>})}
        return <div key={`category-${cat}`} className={`tab${cat == subtab ? " active": ""}${hasNew(cat) ? " new": ""}`}
          onClick={() => { setSubtab(cat) }}>{cat}</div>})}
    </div>
  )
}
