import React from "react"
import { useTranslation } from "react-i18next"
import { Markdown } from "../markdown"
import { closeDocAtom, docAtomFamily, docAtomLegacyFamily, inventoryAtom, InventoryTab, selectedDocTileAtom } from "../../store/inventory-atoms"
import { useAtom } from "jotai"
import { faLock, faXmark } from "@fortawesome/free-solid-svg-icons"
import { NavButton } from "../navigation/nav_button"
import { useGameTranslation } from "../../utils/translation"
import { navigateAcrossWorldsAtom } from "../../store/location-atoms"
import { difficultyAtom } from "../../store/progress-atoms"

/** The `documentation` */
export function Documentation({ type } : {type : InventoryTab}) {
  const { t } = useTranslation()
  const { t: gT } = useGameTranslation()
  const [, navigateAcrossWorlds] = useAtom(navigateAcrossWorldsAtom)
  const [difficulty] = useAtom(difficultyAtom)
  const [, addToInventory] = useAtom(inventoryAtom)

  const [docTile] = useAtom(selectedDocTileAtom)
  const [, closeDoc] = useAtom(closeDocAtom)

  const [{ data: docEntry }] = useAtom(docAtomFamily([type, docTile?.name ?? ""]))
  const [{ data: legacyDocEntry }] = useAtom(docAtomLegacyFamily([type, docTile?.name ?? ""]))

  if (!docTile) return null

  // Set `inventoryDoc` to `null` to close the doc

  return <div className="documentation">
    <NavButton
      icon={faXmark}
      onClick={closeDoc}
      inverted={true}
    />
    { difficulty == 1 && docTile.locked &&
      <NavButton
        icon={faLock}
        title={t("Unlock this item!")}
        onClick={() => {
          console.log(`Adding '${docTile.name}' to the inventory.`)
          addToInventory([docTile.name])
          closeDoc() // note: closing seems better than keeping it open without the lock disappearing
        }}
        className="lock"
        inverted={true} />
    }
    <h1 className="doc">{docTile.displayName}</h1>
    <p><code>{docEntry?.statement ?? legacyDocEntry?.statement}</code></p>
    <Markdown>{gT(docEntry?.content ?? legacyDocEntry?.content ?? "")}</Markdown>
    {/* TODO: The condition below should be updated so that the section
    is displayed whenever it's non-empty. */}
    {docTile.proven && <>
        <h2>Further details</h2>
        <ul>
          {docTile.proven && <li>Proven in: <a onClick={() => {
            if (!docTile.world || !docTile.level) return
            navigateAcrossWorlds(docTile.world, docTile.level)
          }}>{docTile.world} level {docTile.level}</a></li>}
        </ul>
      </>
    }

  </div>
}
