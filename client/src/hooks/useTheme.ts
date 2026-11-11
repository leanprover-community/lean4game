import { useAtomValue } from 'jotai'
import { useLayoutEffect } from 'react'

import { themeAtom } from '../state/preferences-atoms'

/** Applies the `theme` preference as `data-theme` on `<html>`, see `index.css` */
export function useTheme() {
  const theme = useAtomValue(themeAtom)
  // before painting, so the page does not flash in the other theme
  useLayoutEffect(() => {
    const root = document.documentElement
    if (theme === 'auto') delete root.dataset.theme
    else root.dataset.theme = theme
  }, [theme])
}
