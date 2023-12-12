/**
 * @fileOverview Load/save the state to the local browser store
 */

const KEY = "game_progress";

/** Load from browser storage */
export function loadState() {
  try {
    const serializedState = localStorage.getItem(KEY);
    if (!serializedState) return undefined;
    let x = JSON.parse(serializedState);
    // Compatibility: `state.level` has been renamed to `x.games`.
    if (x.level) {
      x.games = x.level
      x.level = undefined
    }
    // Compatibility: code has been moved to `data` and inventory has been added.
    for (var gameState in x.games) {
      if (!x.games[gameState].data) {
        x.games[gameState] = null
      }
    }
    return x
  } catch (e) {
    return undefined;
  }
}

/** Save to browser storage */
export async function saveState(state: any) {
  try {
    const serializedState = JSON.stringify(state)
    localStorage.setItem(KEY, serializedState);
  } catch (e) {
    // Ignore
  }
}

const PREFERENCES_KEY = "preferences"

/** Load from browser storage */
export function loadPreferences() {
  try {
    const serializedState = localStorage.getItem(PREFERENCES_KEY);
    return JSON.parse(serializedState)
  } catch (e) {
    return undefined;
  }
}

export function savePreferences(state: any) {
  try {
    const serializedState = JSON.stringify(state)
    localStorage.setItem(PREFERENCES_KEY, serializedState);
  } catch (e) {
    // Ignore
  }
}
