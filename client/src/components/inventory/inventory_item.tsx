import { faBan, faLock } from "@fortawesome/free-solid-svg-icons"
import { FontAwesomeIcon } from "@fortawesome/react-fontawesome"
import React, { useState } from "react"
import { useTranslation } from "react-i18next"
import { useAppendTypewriterInput } from "../infoview/context"
import { InventoryTile } from "../../state/api"
import { useAtom } from "jotai"
import { selectedDocTileAtom } from "../../store/inventory-atoms"

export function InventoryItem({tile, isTheorem, recent=false, enableAll=false} : {
  tile: InventoryTile,
  isTheorem: boolean,
  recent: boolean,
  enableAll?: boolean,
}) {
  const { t } = useTranslation()
  const [, setDoc] = useAtom(selectedDocTileAtom)
  const icon = (!enableAll && tile.locked) ? <FontAwesomeIcon icon={faLock} /> :
               tile.disabled ? <FontAwesomeIcon icon={faBan} /> : null
  const className = tile.locked ? "locked" : tile.disabled ? "disabled" : tile.new ? "new" : ""
  // Note: This is somewhat a hack as the statement of lemmas comes currently in the form
  // `Namespace.statement_name (x y : Nat) : some type`
  const title = (!enableAll && tile.locked) ? t("Not unlocked yet") :
                tile.disabled ? t("Not available in this level") : (tile.altTitle ? tile.altTitle.substring(tile.altTitle.indexOf(' ') + 1) : '')

  const [copied, setCopied] = useState(false)

  const appendTypewriterInput = useAppendTypewriterInput()
  const handleClick = (ev) => {
    if (appendTypewriterInput(ev.shiftKey, tile.displayName, isTheorem, false)) {
      return
    }
    setDoc(tile)
  }

  const copyItemName = (ev) => {
    navigator.clipboard.writeText(tile.displayName)
    setCopied(true)
    setInterval(() => {
      setCopied(false)
    }, 3000);
    ev.stopPropagation()
  }

return <div className={`item ${className}${enableAll ? ' enabled' : ''}${recent ? ' recent' : ''}`} onClick={handleClick} title={title}>
    {icon} {tile.displayName}
    {/* <div className="copy-button" onClick={copyItemName}>
      {copied ? <FontAwesomeIcon icon={faCheck} /> : <FontAwesomeIcon icon={faClipboard} />}
    </div> */}
  </div>
}
