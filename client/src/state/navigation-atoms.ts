import { atom } from 'jotai'
import { atomEffect } from 'jotai-effect'

import { isMenuPage, locationAtom, routeAtom } from './location-atoms'

/** Controls if the expandable menu in the navigation bar is open or closed */
export const navOpenAtom = atom(false)

export const openNavAtom = atom(null, (_get, set) => {
  set(navOpenAtom, true)
})

export const closeNavAtom = atom(null, (_get, set) => {
  set(navOpenAtom, false)
})

/** The state of the language dropdown */
export const langNavOpenAtom = atom(false)

export const openLangNavAtom = atom(null, (_get, set) => {
  set(langNavOpenAtom, true)
})

export const closeLangNavAtom = atom(null, (_get, set) => {
  set(langNavOpenAtom, false)
})

/** The popups opened from the app bar */
export type PopupType = 'gameInfo' | 'rules' | 'upload' | 'erase'

/** The open popup, at most one at a time */
export const popupAtom = atom<PopupType | null>(null)

/**
 * The last page which is not one of the pages of the menu, e.g. `/g/owner/repo?lang=de`.
 * The menu's pages lead back to it, or to the landing page if they were opened directly.
 */
export const lastPageAtom = atom('/')

/** Keeps `lastPageAtom` up to date */
export const lastPageEffect = atomEffect((get, set) => {
  if (isMenuPage(get(routeAtom))) return
  const location = get(locationAtom)
  const search = location.searchParams?.toString()
  set(lastPageAtom, `${location.pathname ?? '/'}${search ? `?${search}` : ''}`)
})
