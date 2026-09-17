import React, { useEffect } from "react"
import "../../css/inventory.css"
import { InventoryTab, inventoryTabAtom, inventoryTilesAtoms, selectedDocTileAtom, theoremSubtabAtom } from "../../store/inventory-atoms"
import { useAtom } from "jotai"
import { InventoryOverview, InventoryTile, LevelInfo } from "../../store/api"
import { InventorySubTabBar, InventoryTabBar } from "./tab_bars"
import { InventoryList } from "./inventory_list"
import { Documentation } from "./documentation"
import { difficultyAtom } from "../../store/progress-atoms"

/** The panel showing the user's inventory with tactics, definitions, and lemmas */
export function InventoryPanel({levelInfo, visible = true} : {
  levelInfo : LevelInfo | InventoryOverview | undefined,
  visible?: boolean
}) {
  const [tab] = useAtom(inventoryTabAtom)
  const [, setSubtab] = useAtom(theoremSubtabAtom)
  const [doc] = useAtom(selectedDocTileAtom)
  const [, setTheoremInventory] = useAtom(inventoryTilesAtoms[InventoryTab.theorem])
  const [, setTacticInventory] = useAtom(inventoryTilesAtoms[InventoryTab.tactic])
  const [, setDefinitionInventory] = useAtom(inventoryTilesAtoms[InventoryTab.definition])
  const [difficulty] = useAtom(difficultyAtom)

  // TODO: this is some glue since not everything is in jotai yet
  useEffect(() => {
    setTheoremInventory(levelInfo?.lemmas ?? [])
    setTacticInventory(levelInfo?.tactics ?? [])
    setDefinitionInventory(levelInfo?.definitions ?? [])
  }, [levelInfo])

  // If the level specifies `TheoremTab "Nat"`, we switch to this tab on loading.
  // `defaultTab` is `null` or `undefined` otherwise, in which case we don't want to switch.
  useEffect(() => {
    if (levelInfo?.lemmaTab) {
      setSubtab(levelInfo?.lemmaTab)
    }
  }, [levelInfo])

  return <div className={`column inventory-panel inventory panel ${visible ? '' : 'hidden'}`}>
    <InventoryTabBar />
    <InventorySubTabBar />
    <InventoryList tiles={TabContent(tab, levelInfo)} docType={tab} enableAll={difficulty == 0} />
    {doc && <Documentation type={tab} />}

  </div>
}

function TabContent(type: InventoryTab, levelInfo: LevelInfo | InventoryOverview | undefined): InventoryTile[] {
  switch(type) {
    case InventoryTab.theorem: return levelInfo?.lemmas ?? []
    case InventoryTab.tactic: return levelInfo?.tactics ?? []
    case InventoryTab.definition: return levelInfo?.definitions ?? []
    default:
      const _exhaustive: never = type
      return []
  }
}
