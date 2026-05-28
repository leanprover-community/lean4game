import { faBan, faCheck, faClipboard, faLock, faReply } from "@fortawesome/free-solid-svg-icons"
import { FontAwesomeIcon } from "@fortawesome/react-fontawesome"
import React, { useState } from "react"
import { useTranslation } from "react-i18next"
import { InventoryTile } from "../../store/api"
import { useAtom } from "jotai"
import { selectedDocTileAtom } from "../../store/inventory-atoms"
import { levelIdAtom } from "../../store/location-atoms"
import { typewriterAtom, typewriterContentAtom } from "../../store/editor-atoms"
import { preferencesAtom } from "../../store/preferences-atoms"

export function InventoryItem({tile, isTheorem, recent=false, enableAll=false} : {
  tile: InventoryTile,
  isTheorem: boolean,
  recent: boolean,
  enableAll?: boolean,
}) {
  const { t } = useTranslation()
  const [, setDoc] = useAtom(selectedDocTileAtom)
  const [levelId] = useAtom(levelIdAtom)
  const [typewriterContent,] = useAtom(typewriterContentAtom)
  const [, setTypewriter] = useAtom(typewriterAtom)
  const [{ isSuggestionsMobileMode }] = useAtom(preferencesAtom)

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
  // Step 1: Copy over from infoview/context
  // Step 2: Auto-import the used atoms
  // Step 3: Copy SUFFIX and PREFIX OVERRIDES into function scpe
  // Step 4: Reformulate parameters to adhere to old implementation
  // Step 5: Relocate useAtoms into enclosing scope of function to stop infinite re-renders
  function appendTypewriterInput(shiftKey: boolean, suffix: string, isTheorem: boolean, isAssumption: boolean) {
    const SUFFIX_OVERRIDES: Record<string, string> = {
      "induction": "generalizing",
      "left": ".left",
      "rewrite": "←",
      "right": ".right",
      "rw": "←",
    }

    const PREFIX_OVERRIDES: Record<string, string> = {
      "by_cases": "by_cases this :",
      "contrapose": "contrapose!",
      "have": "have :",
      "obtain": "obtain ⟨⟩ :=",
      "rewrite": "rw []",
      "rw": "rw []",
      "simp": "simp only []",
    }

    //return (shiftKey: boolean, suffix: string, isTheorem: boolean, isAssumption: boolean) => {
      if (!isSuggestionsMobileMode && !shiftKey) {
        return false
      }
      // Automagically detect and adjust punctuation for mobile keyboardless usage
      let _typewriter = typewriterContent.trim()

      if (!typewriterContent.length) {
        _typewriter = Object.hasOwn(PREFIX_OVERRIDES, suffix) ? PREFIX_OVERRIDES[suffix] : isTheorem ? `rw [${suffix}]` : suffix
        setTypewriter(_typewriter + " ")
        return true
      }

        suffix = !isAssumption && Object.hasOwn(SUFFIX_OVERRIDES, suffix) ? SUFFIX_OVERRIDES[suffix] : suffix
        if (suffix === "ℕ") {
          if (/ \d$/.test(_typewriter)) {
            suffix = ((+_typewriter.slice(-2) + 1) % 10).toString()
            _typewriter = _typewriter.slice(0, -2)
          } else {
            suffix = "0"
          }
          suffix = " " + suffix
        } else if (suffix === "∈" && _typewriter.endsWith("∈")) {
          suffix = " {} "
        } else if (isAssumption && /^apply |^symm|^push_neg/.test(_typewriter)) {
          suffix = " at " + suffix
        } else if (suffix === "have") {
          suffix = _typewriter === "have :" ? "=" : " :="
        } else if (/[\]}]$/.test(_typewriter)) {
          if (isAssumption) {
            suffix = " at " + suffix
          } else {
            const closing = _typewriter.slice(-1)
            _typewriter = _typewriter.slice(0, -1)
            if (suffix === "←") {
              const imbalance = (_typewriter.match(/\(/)?.length ?? 0) - (_typewriter.match(/\)/)?.length ?? 0)
              suffix = /[[,({]$/.test(_typewriter) ? "←" : /\([^)]*$/.test(_typewriter) ? ")" : " ("
            } else {
              if (!/[[,({]$/.test(_typewriter)) {
                suffix = (isTheorem && !_typewriter.endsWith("←") && closing === "]" ? ", " : /^[ᶜ.]/.test(suffix) ? "" : " ") + suffix
              }
            }
            suffix = suffix + closing
          }
        } else if (!/^[ᶜ.]/.test(suffix)) {
          suffix = " " + suffix
        }
        setTypewriter(`${_typewriter}${suffix} `.trimStart())
        return true
      //}
  }

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
