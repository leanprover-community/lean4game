import React, { useEffect, useState } from "react"
import { useTranslation } from "react-i18next"
import { InventoryOverview, InventoryTile, LevelInfo } from "../../state/api"
// import { InventoryList } from "./InventoryList"
import { inventorySubtabAtom, InventoryTab, inventoryTabAtom, inventoryTilesAtoms, selectedDocTileAtom } from "../../store/inventory-atoms"
import { useAtom } from "jotai"
import { Tab } from "@mui/material"
import { InventorySubTabBar, InventoryTabBar } from "./TabBars"
import { InventoryList } from "./InventoryList"
import { Documentation } from "./Documentation"


function TabContent(type: InventoryTab, levelInfo: LevelInfo | InventoryOverview | undefined): InventoryTile[] {
  switch(type) {
    case InventoryTab.theorem: return levelInfo?.lemmas ?? []
    case InventoryTab.tactic: return levelInfo?.tactics ?? []
    case InventoryTab.definition: return levelInfo?.definitions ?? []
    default:
      const _exhaustive: never = type
  }
}

export function Inventory({levelInfo, enableAll=false} :
  {
    levelInfo: LevelInfo | InventoryOverview | undefined,
    enableAll?: boolean,
  }) {
  const { t } = useTranslation()
  const [tab, setTab] = useAtom(inventoryTabAtom)
  const [doc] = useAtom(selectedDocTileAtom)
  const [, setTheoremInventory] = useAtom(inventoryTilesAtoms[InventoryTab.theorem])
  const [, setTacticInventory] = useAtom(inventoryTilesAtoms[InventoryTab.tactic])
  const [, setDefinitionInventory] = useAtom(inventoryTilesAtoms[InventoryTab.definition])

  const subTabs = [...new Set(TabContent(tab, levelInfo).map(item => item.category))]

  // TODO: this is some glue since no everything is in jotai yet
  useEffect(() => {
    setTheoremInventory(levelInfo?.lemmas ?? [])
    setTacticInventory(levelInfo?.tactics ?? [])
    setDefinitionInventory(levelInfo?.definitions ?? [])
  }, [levelInfo])

  return (
    <div className="inventory">
      <InventoryTabBar />
      <InventorySubTabBar />
      {levelInfo &&
        <InventoryList tiles={TabContent(tab, levelInfo)} docType={tab} enableAll={enableAll} />
      }
    </div>
  )
}
