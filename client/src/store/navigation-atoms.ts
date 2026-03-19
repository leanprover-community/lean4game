import { atom } from "jotai";

/** Controls if the expandable menu in the navigation bar is open or closed */
export const navOpenAtom = atom(false);

export const openNavAtom = atom(null, (get, set) => {
  set(navOpenAtom, true)
})

export const closeNavAtom = atom(null, (get, set) => {
  set(navOpenAtom, false)
})

/** The state of the language dropdown */
export const langNavOpenAtom = atom(false);

export const openLangNavAtom = atom(null, (get, set) => {
  set(langNavOpenAtom, true)
})

export const closeLangNavAtom = atom(null, (get, set) => {
  set(langNavOpenAtom, false)
})
