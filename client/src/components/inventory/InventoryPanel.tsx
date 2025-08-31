import React, { useContext, useEffect, useState } from "react"
import { GameIdContext } from "../../app"
import { Documentation } from "./Documentation"
import { Inventory } from "./Inventory"
import "../../css/inventory.css"

/** The panel (on the welcome page) showing the user's inventory with tactics, definitions, and lemmas */
export function InventoryPanel({levelInfo, visible = true}) {
  const gameId = useContext(GameIdContext)

  const [lemmaTab, setLemmaTab] = useState(levelInfo?.lemmaTab)

  // The inventory is overlayed by the doc entry of a clicked item
  const [inventoryDoc, setInventoryDoc] = useState<{name: string, type: string}>(null)
  // Set `inventoryDoc` to `null` to close the doc
  function closeInventoryDoc() {setInventoryDoc(null)}

    useEffect(() => {
    // If the level specifies `LemmaTab "Nat"`, we switch to this tab on loading.
    // `defaultTab` is `null` or `undefined` otherwise, in which case we don't want to switch.
    if (levelInfo?.lemmaTab) {
      setLemmaTab(levelInfo?.lemmaTab)
    }}, [levelInfo])

  return <div className={`column inventory-panel ${visible ? '' : 'hidden'}`}>
    {inventoryDoc ?
      <Documentation name={inventoryDoc.name} type={inventoryDoc.type} handleClose={closeInventoryDoc}/>
      :
      <Inventory levelInfo={levelInfo} openDoc={setInventoryDoc} enableAll={true} lemmaTab={lemmaTab} setLemmaTab={setLemmaTab}/>
    }
  </div>
}
