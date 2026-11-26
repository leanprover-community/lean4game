import { useAtomValue } from 'jotai'
import { type RefObject, useEffect, useRef } from 'react'

import { focusAtEnd } from '../Masks/Typewriter/CommandInput'
import { levelIdAtom, worldIdAtom } from '../state/location-atoms'
import { mobileAtom } from '../state/preferences-atoms'

/** Whether `element` is a field the player types into */
function isEditable(element: Element | null) {
  return (
    element instanceof HTMLInputElement ||
    element instanceof HTMLTextAreaElement ||
    (element instanceof HTMLElement && element.isContentEditable)
  )
}

/**
 * Focus the selected input as soon as `ready` turns true.
 *
 * Not on mobile (as this would trigger the keyboard) and not
 * if the player is already typing.
 */
export function useFocusOnLevelOpen(
  ref: RefObject<HTMLTextAreaElement | null>,
  ready: boolean,
) {
  const worldId = useAtomValue(worldIdAtom)
  const levelId = useAtomValue(levelIdAtom)
  const mobile = useAtomValue(mobileAtom)
  const level = `${worldId}/${levelId}`
  const focusedFor = useRef<string | null>(null)

  useEffect(() => {
    if (!ready || mobile || focusedFor.current === level) return
    const textarea = ref.current
    if (!textarea) return
    focusedFor.current = level
    const active = document.activeElement
    if (active !== textarea && isEditable(active)) return
    focusAtEnd(textarea)
  }, [ref, ready, mobile, level])
}
