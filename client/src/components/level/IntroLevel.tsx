import { useAtom } from "jotai"
import { useTranslation } from "react-i18next"
import { gameIdAtom, worldIdAtom } from "../../store/location-atoms"
import { mobileAtom } from "../../store/preferences-atoms"
import { inventoryOverviewAtom } from "../../store/inventory-atoms"
import { gameInfoAtom } from "../../store/query-atoms"
import { CircularProgress } from "@mui/material"
import { LevelAppBar } from "../app_bar"
import React from "react"
import { IntroPanel } from "../chat/IntroPanel"
import Split from "react-split"
import path from 'path'
import { InventoryPanel } from "../inventory/inventory_panel"


/** The site with the introduction text of a world */
export function IntroLevel() {
  let { t } = useTranslation()

  const [gameId] = useAtom(gameIdAtom)
  const [worldId] = useAtom(worldIdAtom)

  const [mobile] = useAtom(mobileAtom)

  const [{ data: gameInfo, isLoading: isLoadingGameInfo }] = useAtom(gameInfoAtom)


  let image: string = worldId ? gameInfo?.worlds?.nodes[worldId]?.image ?? "" : ""

  return <>
    <LevelAppBar isLoading={isLoadingGameInfo} levelTitle={t("Introduction")} />
    {isLoadingGameInfo ?
      <div className="app-content loading"><CircularProgress /></div>
    : mobile ?
        <IntroPanel />
      :
        <Split minSize={0} snapOffset={200} sizes={[25, 50, 25]} className={`app-content level`}>
          <IntroPanel />
          <div className="world-image-container empty center">
            {image && gameId &&
              <img className="contain" src={path.join("data", gameId, image)} alt="" />
            }

          </div>
          <InventoryPanel />
        </Split>
      }

  </>
}
