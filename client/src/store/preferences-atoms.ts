import { atom } from "jotai";
import { atomWithStorage, createJSONStorage } from "jotai/utils";

export interface Preferences {
  layout: "mobile" | "auto" | "desktop"
  isSavePreferences: boolean
  language: string
  isSuggestionsMobileMode: boolean
  useFlags: boolean
}

export function getWindowDimensions() {
  const {innerWidth: width, innerHeight: height } = window
  return {width, height}
}

export const AUTO_SWITCH_THRESHOLD = 800

const defaultPreferences: Preferences = {
  layout: "auto",
  isSavePreferences: false,
  language: import.meta.env.VITE_CLIENT_DEFAULT_LANGUAGE || "en",
  isSuggestionsMobileMode: 'ontouchstart' in document.documentElement,
  useFlags: false,
};

const storage = createJSONStorage<Preferences>(() => localStorage)

const conditionalStorage = {
  ...storage,
  setItem: (key: string, value: Preferences) => {
    if (value.isSavePreferences) {
      storage.setItem(key, value)
    } else {
      storage.removeItem(key)
    }
  },
}

/**
 * User preferences synchronised with local storage
 */
export const preferencesAtom = atomWithStorage<Preferences>(
  'preferences',
  defaultPreferences,
  conditionalStorage,
  { getOnInit: true }
)

const widthBelowThresholdAtom = atom(false)
widthBelowThresholdAtom.onMount = set => {
  const mq = window.matchMedia(`(max-width: ${AUTO_SWITCH_THRESHOLD}px)`)
  const update = () => set(mq.matches)

  update()
  mq.addEventListener("change", update)

  return () => mq.removeEventListener("change", update)
}

export const mobileAtom = atom(get => {
  const layout = get(preferencesAtom).layout
  const widthBelowThreshold = get(widthBelowThresholdAtom)
  switch (layout) {
    case "mobile": return true
    case "desktop": return false
    case "auto": return widthBelowThreshold
  }
})
