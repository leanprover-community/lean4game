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
    // Complatibilty because `state.level` has been renamed to `x.games`.
    // TODO: Does this work?
    if (x.level) {
      x.games = x.level
      x.level = undefined
    }
    return x
  } catch (e) {
    return undefined;
  }
}

/** Save to browser storage */
export async function saveState(state: any) {
  try {
    const serializedState = JSON.stringify(state);
    localStorage.setItem(KEY, serializedState);
  } catch (e) {
    // Ignore
  }
}
