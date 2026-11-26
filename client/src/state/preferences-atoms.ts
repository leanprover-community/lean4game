import { atom } from 'jotai'
import { atomWithStorage } from 'jotai/utils'

import { conditionalStorage, isDefault } from '../utils/conditional-storage'

export interface Preferences {
  layout: 'mobile' | 'auto' | 'desktop'
  useFlags: boolean
  /** `auto` follows the system setting */
  theme: 'light' | 'auto' | 'dark'
  showLockedInventory: boolean
}

export function getWindowDimensions() {
  const { innerWidth: width, innerHeight: height } = window
  return { width, height }
}

export const AUTO_SWITCH_THRESHOLD = 800

const defaultPreferences: Preferences = {
  layout: 'auto',
  useFlags: false,
  theme: 'auto',
  showLockedInventory: true,
}

/**
 * User preferences synchronised with local storage
 */
export const preferencesAtom = atomWithStorage<Preferences>(
  'preferences',
  defaultPreferences,
  conditionalStorage(defaultPreferences),
  { getOnInit: true },
)

/** Whether all preferences have their default value */
export const isDefaultPreferencesAtom = atom(get =>
  isDefault(get(preferencesAtom), defaultPreferences),
)

const widthBelowThresholdAtom = atom(false)
widthBelowThresholdAtom.onMount = set => {
  const mq = window.matchMedia(`(max-width: ${AUTO_SWITCH_THRESHOLD}px)`)
  const update = () => set(mq.matches)

  update()
  mq.addEventListener('change', update)

  return () => mq.removeEventListener('change', update)
}

export const mobileAtom = atom(get => {
  const layout = get(preferencesAtom).layout
  const widthBelowThreshold = get(widthBelowThresholdAtom)
  switch (layout) {
    case 'mobile':
      return true
    case 'desktop':
      return false
    case 'auto':
      return widthBelowThreshold
  }
})

/** The colour theme */
export const themeAtom = atom(get => get(preferencesAtom).theme)
