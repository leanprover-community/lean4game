import React, { useState } from "react"
import { useTranslation } from "react-i18next"
import { InventoryOverview, LevelInfo } from "../../state/api"
import { InventoryList } from "./InventoryList"

export function Inventory({levelInfo, openDoc, lemmaTab, setLemmaTab, enableAll=false} :
  {
    levelInfo: LevelInfo|InventoryOverview,
    openDoc: (props: {name: string, type: string}) => void,
    lemmaTab: any,
    setLemmaTab: any,
    enableAll?: boolean,
  }) {
  const { t } = useTranslation()

  // TODO: this state should be preserved when loading a different level.
  const [tab, setTab] = useState<"tactic"|"theorem"|"definition">("theorem")

  let newTheorems = levelInfo?.lemmas?.filter(item => item.new).length > 0
  let newTactics = levelInfo?.tactics?.filter(item => item.new).length > 0
  let newDefinitions = levelInfo?.definitions?.filter(item => item.new).length > 0

  return (
    <div className="inventory">
      <div className="tab-bar major">
        <div className={`tab${(tab == "theorem") ? " active": ""}${newTheorems ? " new" : ""}`} onClick={() => { setTab("theorem") }}>{t("Theorems")}</div>
        <div className={`tab${(tab == "tactic") ? " active": ""}${newTactics ? " new" : ""}`} onClick={() => { setTab("tactic") }}>{t("Tactics")}</div>
        <div className={`tab${(tab == "definition") ? " active": ""}${newDefinitions ? " new" : ""}`} onClick={() => { setTab("definition") }}>{t("Definitions")}</div>
      </div>
      { (tab == "theorem") && levelInfo?.lemmas &&
        <InventoryList items={levelInfo?.lemmas} docType="Lemma" openDoc={openDoc} level={levelInfo} enableAll={enableAll} tab={lemmaTab} setTab={setLemmaTab}/>
      }
      { (tab == "tactic") && levelInfo?.tactics &&
        <InventoryList items={levelInfo?.tactics} docType="Tactic" openDoc={openDoc} enableAll={enableAll}/>
      }
      { (tab == "definition") && levelInfo?.definitions &&
        <InventoryList items={levelInfo?.definitions} docType="Definition" openDoc={openDoc} enableAll={enableAll}/>
      }
    </div>
  )
}
