import { atom } from 'jotai'

/** Type of valid popups. */
export enum PopupType {
  erase = 'erase',
  impressum = 'impressum',
  info = 'info',
  preferences = 'preferences',
  privacy = 'privacy',
  rules = 'rules',
  upload = 'upload',
}

/** Currently open popup. Set to `null` to close all. */
export const popupAtom = atom(null as PopupType | null)
