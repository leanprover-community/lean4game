import { faBan, faCheck, faClipboard, faLock, faReply } from "@fortawesome/free-solid-svg-icons"
import { FontAwesomeIcon } from "@fortawesome/react-fontawesome"
import React, { useState } from "react"
import { useTranslation } from "react-i18next"
import { InventoryTile } from "../../store/api"
import { useAtom } from "jotai"
import { selectedDocTileAtom } from "../../store/inventory-atoms"
import { levelIdAtom } from "../../store/location-atoms"

export function InventoryItem({tile, isTheorem, recent=false, enableAll=false} : {
  tile: InventoryTile,
  isTheorem: boolean,
  recent: boolean,
  enableAll?: boolean,
}) {
  const { t } = useTranslation()
  const [, setDoc] = useAtom(selectedDocTileAtom)
  const [levelId] = useAtom(levelIdAtom)

  const insertable: boolean = (levelId ?? 0) > 0 && (enableAll || !(tile.locked || tile.disabled))

  const icon = (!enableAll && tile.locked) ? <FontAwesomeIcon icon={faLock} /> :
               tile.disabled ? <FontAwesomeIcon icon={faBan} /> : null
  const className = tile.locked ? "locked" : tile.disabled ? "disabled" : tile.new ? "new" : ""
  // Note: This is somewhat a hack as the statement of lemmas comes currently in the form
  // `Namespace.statement_name (x y : Nat) : some type`
  const title = (!enableAll && tile.locked) ? t("Not unlocked yet") :
                tile.disabled ? t("Not available in this level") : (tile.altTitle ? tile.altTitle.substring(tile.altTitle.indexOf(' ') + 1) : '')

  const [inserted, setInserted] = useState(false)

  // const appendTypewriterInput = useAppendTypewriterInput()

  // FIXME: implement
  function appendTypewriterInput(a: any, b: any, c: any, d: any) {}


  const handleClick = (ev: any) => {setDoc(tile)}

  const insertItemName = (ev: any) => {
    // navigator.clipboard.writeText(tile.displayName)
    appendTypewriterInput(ev.shiftKey, tile.displayName, isTheorem, false)
    setInserted(true)
    setInterval(() => {
      setInserted(false)
    }, 3000);
    ev.stopPropagation()
  }

return <div className={`item ${className}${enableAll ? ' enabled' : ''}${recent ? ' recent' : ''}`} onClick={handleClick} title={title}>
    {icon} {tile.displayName}
    {insertable &&
    <button
        className="insert-button"
        title={`insert '${tile.displayName}'`}
        onClick={insertItemName}
    >
      {inserted ? <FontAwesomeIcon icon={faCheck} /> : <FontAwesomeIcon icon={faReply} />}
    </button> }
  </div>
}
