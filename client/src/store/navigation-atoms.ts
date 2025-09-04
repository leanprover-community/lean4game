import { atom } from "jotai";

/** Controlls if the expandable menu in the navigation bar is open or closed */
export const navOpenAtom = atom(false);

export const openNavAtom = atom(null, (get, set) => {
  set(navOpenAtom, true)
})

export const closeNavAtom = atom(null, (get, set) => {
  set(navOpenAtom, false)
})
