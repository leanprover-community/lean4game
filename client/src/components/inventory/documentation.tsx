import React, { useContext } from "react"
import { useTranslation } from "react-i18next"
import { GameIdContext } from "../../app"
import { useLoadDocQuery } from "../../state/api"
import { Markdown } from "../markdown"
import { useAppDispatch } from "../../hooks"
import { useSelector } from "react-redux"
import { changedInventory, selectDifficulty, selectInventory } from "../../state/progress"
import { closeDocAtom, InventoryTab, selectedDocTileAtom } from "../../store/inventory-atoms"
import { useAtom } from "jotai"
import { faLock, faXmark } from "@fortawesome/free-solid-svg-icons"
import { NavButton } from "../navigation/nav_button"
import { store } from "../../state/store"
import { useGameTranslation } from "../../utils/translation"

/** The `documentation` */
export function Documentation({ type } : {type : InventoryTab}) {
  const { t } = useTranslation()
  const { t: gT } = useGameTranslation()
  const dispatch = useAppDispatch()
  const gameId = useContext(GameIdContext)
  const difficulty = useSelector(selectDifficulty(gameId))

  const [docTile] = useAtom(selectedDocTileAtom)
  const [, closeDoc] = useAtom(closeDocAtom)

  // // const docEntry = useLoadDocQuery({game: gameId, type: type, name: name})
  // let { docTile, setDocTile } = useContext(InventoryContext)

  const docEntry = useLoadDocQuery({game: gameId, name: docTile.name, type: type })
  let inv: string[] = useSelector(selectInventory(gameId))

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
          dispatch(changedInventory({ game: gameId, inventory: [...inv, docTile.name] }))
          closeDoc() // note: closing seems better than keeping it open without the lock disappearing
        }}
        className="lock"
        inverted={true} />
    }
    <h1 className="doc">{docTile.displayName}</h1>
    <p><code>{docEntry.data?.statement}</code></p>
    <Markdown>{gT(docEntry.data?.content)}</Markdown>
    {/* TODO: The condition below should be updated so that the section
    is displayed whenever it's non-empty. */}
    {docTile.proven && <>
        <h2>Further details</h2>
        <ul>
          {docTile.proven && <li>Proven in: <a href={`#/${gameId}/world/${docTile.world}/level/${docTile.level}`}>{docTile.world} level {docTile.level}</a></li>}
        </ul>
      </>
    }

  </div>
}
