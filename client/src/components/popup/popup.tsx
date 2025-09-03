import * as React from 'react'
import { useAtom } from 'jotai'
import { popupAtom, PopupType } from '../../store/popup-atoms'
import { ImpressumPopup } from './impressum'
import { InfoPopup } from './info'
import '../../css/popup.css'
import { PrivacyPolicyPopup } from './privacy'
import { UploadPopup } from './upload'
import { PreferencesPopup } from './preferences'
import { RulesHelpPopup } from './rules_help'

/**
 * To create a new popup on needs add a option to `PopupType`,
 * and then define its content in `getPopupContent` below.
 *
 * Popups can be opened by setting the `popupAtom` to the popup's type.
 */

/** The content of the current popup. */
function getPopupContent(popup: PopupType) {
  switch(popup) {
    case PopupType.erase:
      return <></>
    case PopupType.impressum:
      return <ImpressumPopup />
    case PopupType.info:
      return <InfoPopup />
    case PopupType.preferences:
      return <PreferencesPopup />
    case PopupType.privacy:
      return <PrivacyPolicyPopup />
    case PopupType.rules:
      return <RulesHelpPopup />
    case PopupType.upload:
      return <UploadPopup />
    default:
      // Hack: this throws a TS error when cases are missed.
      const _exhaustive: never = popup
  }
}

/** A popup displayed over the entire page. */
export function Popup () {
  const [popup, setPopup] = useAtom(popupAtom)

  function closePopup() {
    setPopup(null)
  }

  if (!popup) {return null}

  return <div className="modal-wrapper">
  <div className="modal-backdrop" onClick={closePopup} />
  <div className="modal">
    <div className="codicon codicon-close modal-close" onClick={closePopup}></div>
    {getPopupContent(popup)}
  </div>
</div>
}
