import React, { useContext, useEffect, useState } from "react"
import { GameIdContext } from "../../app"
import { Inventory } from "./Inventory"
import "../../css/inventory.css"
import { inventoryTabAtom, selectedDocTileAtom, theoremSubtabAtom } from "../../store/inventory-atoms"
import { useAtom } from "jotai"
import { InventoryOverview, LevelInfo } from "../../state/api"
import { Documentation } from "./Documentation"

/** The panel (on the welcome page) showing the user's inventory with tactics, definitions, and lemmas */
export function InventoryPanel({levelInfo, visible = true} : {
  levelInfo? : LevelInfo | InventoryOverview,
  visible: boolean
}) {
  const [tab, setTab] = useAtom(inventoryTabAtom)
  const [, setSubtab] = useAtom(theoremSubtabAtom)
  const [doc] = useAtom(selectedDocTileAtom)

  // If the level specifies `TheoremTab "Nat"`, we switch to this tab on loading.
  // `defaultTab` is `null` or `undefined` otherwise, in which case we don't want to switch.
  useEffect(() => {
    if (levelInfo?.lemmaTab) {
      setSubtab(levelInfo?.lemmaTab)
    }
  }, [levelInfo])

  return <div className={`column inventory-panel ${visible ? '' : 'hidden'}`}>
    {levelInfo && <Inventory levelInfo={levelInfo} enableAll={true} />}
    { doc && <Documentation type={tab} />}

  </div>
}
