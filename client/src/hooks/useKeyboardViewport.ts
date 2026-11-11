import { useEffect } from 'react'

/**
 * Keeps the app in the part of the screen above the on-screen keyboard, so that the
 * header and e.g. the typewriter's input line stay visible and only the content between
 * them scrolls.
 *
 * Android's browsers do this by themselves with `interactive-widget=resizes-content` in
 * the viewport meta tag of `index.html`. iOS Safari ignores it: it keeps the page's height
 * and scrolls the whole page to show the focused field, which moves the header out of
 * view. There, the visual viewport (the part above the keyboard) shrinks, so its height
 * becomes the app's height, see `--app-height` in `index.css`, and the page is scrolled
 * back to the top.
 *
 * Not while the page is zoomed in, which also shrinks the visual viewport.
 */
export function useKeyboardViewport() {
  useEffect(() => {
    // missing in old browsers
    const viewport = window.visualViewport
    const style = document.documentElement.style
    const update = () => {
      if (!viewport) return
      if (Math.abs(viewport.scale - 1) > 0.01) {
        style.removeProperty('--app-height')
        return
      }
      style.setProperty('--app-height', `${viewport.height}px`)
      if (window.scrollY !== 0) window.scrollTo(0, 0)
    }
    update()
    viewport?.addEventListener('resize', update)
    viewport?.addEventListener('scroll', update)
    return () => {
      viewport?.removeEventListener('resize', update)
      viewport?.removeEventListener('scroll', update)
      style.removeProperty('--app-height')
    }
  }, [])
}
