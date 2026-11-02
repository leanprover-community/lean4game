import { type Getter, atom } from 'jotai'

import { readGameIntroAtom } from './chat-atoms'
import { locationAtom, routeAtom } from './location-atoms'
import { mobileAtom } from './preferences-atoms'

/**
 * Whether a side panel of `PanelLayout` is open. By default the side panels are open on
 * desktop and closed on mobile, unless `openOnMobile`. A choice of the player lasts
 * until the layout switches between desktop and mobile, and on mobile, where a side
 * panel covers the page, until going to another page.
 */
function panelOpenAtom(openOnMobile: (get: Getter) => boolean = () => false) {
  const choiceAtom = atom<{
    mobile: boolean
    open: boolean
    pathname?: string
  } | null>(null)
  return atom(
    get => {
      const mobile = get(mobileAtom)
      const choice = get(choiceAtom)
      const pathname = mobile ? get(locationAtom).pathname : undefined
      if (choice?.mobile === mobile && choice.pathname === pathname)
        return choice.open
      return !mobile || openOnMobile(get)
    },
    (get, set, open: boolean) => {
      const mobile = get(mobileAtom)
      const pathname = mobile ? get(locationAtom).pathname : undefined
      set(choiceAtom, { mobile, open, pathname })
    },
  )
}

/**
 * On mobile, the chat is open on a world's introduction and conclusion, and on the game
 * overview until its introduction was read
 */
export const leftPanelOpenAtom = panelOpenAtom(get => {
  const { page } = get(routeAtom)
  return (
    page === 'world' ||
    page === 'worldConclusion' ||
    (page === 'game' && !get(readGameIntroAtom))
  )
})
export const rightPanelOpenAtom = panelOpenAtom()
