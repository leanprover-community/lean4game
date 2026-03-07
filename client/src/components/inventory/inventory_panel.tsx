import React, { useContext, useEffect } from "react"
import "../../css/inventory.css"
import { InventoryTab, inventoryTabAtom, inventoryTilesAtoms, selectedDocTileAtom, theoremSubtabAtom, userInventoryAtom } from "../../store/inventory-atoms"
import { useAtom } from "jotai"
import { InventoryOverview, InventoryTile, LevelInfo } from "../../state/api"
import { selectDifficulty, selectInventory } from "../../state/progress"
import { store } from "../../state/store"
import { gameIdAtom, levelIdAtom, worldIdAtom } from "../../store/location-atoms"
import { InventorySubTabBar, InventoryTabBar } from "./tab_bars"
import { InventoryList } from "./inventory_list"
import { useSelector } from "react-redux"
import { Documentation } from "./documentation"

/** The panel showing the user's inventory with tactics, definitions, and lemmas */
export function InventoryPanel({levelInfo, visible = true} : {
  levelInfo : LevelInfo | InventoryOverview | undefined,
  visible?: boolean
}) {
  const [gameId] = useAtom(gameIdAtom)
  const inventory: string[] = useSelector(selectInventory(gameId))

  const [tab] = useAtom(inventoryTabAtom)
  const [, setSubtab] = useAtom(theoremSubtabAtom)
  const [doc] = useAtom(selectedDocTileAtom)

  const [, setTheoremInventory] = useAtom(inventoryTilesAtoms[InventoryTab.theorem])
  const [, setTacticInventory] = useAtom(inventoryTilesAtoms[InventoryTab.tactic])
  const [, setDefinitionInventory] = useAtom(inventoryTilesAtoms[InventoryTab.definition])
  const [, setUserInventory] = useAtom(userInventoryAtom)

  const difficulty = useSelector(selectDifficulty(gameId))

  // TODO: this is some glue since not everything is in jotai yet
  useEffect(() => {
    setTheoremInventory(levelInfo?.lemmas ?? [])
    setTacticInventory(levelInfo?.tactics ?? [])
    setDefinitionInventory(levelInfo?.definitions ?? [])
  }, [levelInfo])

  // Some glue as the user inventory isn't fully in jotai yet
  useEffect(() => {
    setUserInventory(inventory)
  }, [inventory])

  // If the level specifies `TheoremTab "Nat"`, we switch to this tab on loading.
  // `defaultTab` is `null` or `undefined` otherwise, in which case we don't want to switch.
  useEffect(() => {
    if (levelInfo?.lemmaTab) {
      setSubtab(levelInfo?.lemmaTab)
    }
  }, [levelInfo])

  return <div className={`column inventory-panel ${visible ? '' : 'hidden'}`}>
    <div className="inventory">
      <InventoryTabBar />
      <InventorySubTabBar />
      {levelInfo &&
        <InventoryList tiles={TabContent(tab, levelInfo)} docType={tab} enableAll={difficulty == 0} />
      }
    </div>
    { doc && <Documentation type={tab} />}

  </div>
}

function TabContent(type: InventoryTab, levelInfo: LevelInfo | InventoryOverview | undefined): InventoryTile[] {
  switch(type) {
    case InventoryTab.theorem: return levelInfo?.lemmas ?? []
    case InventoryTab.tactic: return levelInfo?.tactics ?? []
    case InventoryTab.definition: return levelInfo?.definitions ?? []
    default:
      const _exhaustive: never = type
  }
}
