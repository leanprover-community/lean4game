import { atom } from 'jotai'
import { ImpressumPopup } from '../components/popup/impressum'

/** Type of valid popups. */
export enum PopupType {
  impressum = 'impressum',
  info = 'info',
  privacy = 'privacy',
  upload = 'upload',
}

/** Currently open popup. Set to `null` to close all. */
export const popupAtom = atom(null as PopupType | null)
