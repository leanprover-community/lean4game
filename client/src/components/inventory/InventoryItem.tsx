import { faBan, faCheck, faClipboard, faLock } from "@fortawesome/free-solid-svg-icons"
import { FontAwesomeIcon } from "@fortawesome/react-fontawesome"
import React, { useState } from "react"
import { useTranslation } from "react-i18next"
import { useAppendTypewriterInput } from "../infoview/context"

export function InventoryItem({item, name, displayName, locked, disabled, newly, showDoc, isTheorem, recent=false, enableAll=false}) {
  const { t } = useTranslation()
  const icon = locked ? <FontAwesomeIcon icon={faLock} /> :
               disabled ? <FontAwesomeIcon icon={faBan} /> : item.st
  const className = locked ? "locked" : disabled ? "disabled" : newly ? "new" : ""
  // Note: This is somewhat a hack as the statement of lemmas comes currently in the form
  // `Namespace.statement_name (x y : Nat) : some type`
  const title = locked ? t("Not unlocked yet") :
                disabled ? t("Not available in this level") : (item.altTitle ? item.altTitle.substring(item.altTitle.indexOf(' ') + 1) : '')

  const [copied, setCopied] = useState(false)

  const appendTypewriterInput = useAppendTypewriterInput()
  const handleClick = (ev) => {
    if (!enableAll && locked || appendTypewriterInput(ev.shiftKey, displayName, isTheorem, false)) {
      return
    }
    showDoc()
  }

  const copyItemName = (ev) => {
    navigator.clipboard.writeText(displayName)
    setCopied(true)
    setInterval(() => {
      setCopied(false)
    }, 3000);
    ev.stopPropagation()
  }

return <div className={`item ${className}${enableAll ? ' enabled' : ''}${recent ? ' recent' : ''}`} onClick={handleClick} title={title}>
    {icon} {displayName}
    <div className="copy-button" onClick={copyItemName}>
      {copied ? <FontAwesomeIcon icon={faCheck} /> : <FontAwesomeIcon icon={faClipboard} />}
    </div>
  </div>
}
