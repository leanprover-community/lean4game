import * as React from 'react'
import { createContext } from 'react'

/** The context which manages if a popup is shown.
 * If `popupContent` is `null`, the popup is closed.
 */
export const PopupContext = createContext<{
  popupContent: string,
  setPopupContent: React.Dispatch<React.SetStateAction<string>>
}>({
  popupContent: null,
  setPopupContent: () => {}
})
