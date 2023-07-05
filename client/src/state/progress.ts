/**
 * @fileOverview Defines the user progress which is loaded from the browser store and kept
 */
import { createSlice } from '@reduxjs/toolkit'
import type { PayloadAction } from '@reduxjs/toolkit'
import { loadState } from "./local_storage";

interface Selection {
  selectionStartLineNumber: number,
  selectionStartColumn: number,
  positionLineNumber: number
  positionColumn: number
}
interface LevelProgressState {
  code: string,
  selections: Selection[],
  completed: boolean
}

export interface GameProgressState {
  [world: string] : {[level: number]: LevelProgressState}
}

/** The progress made on all lean4-games */
interface ProgressState {
  games: {[game: string]: GameProgressState}
}

const initialProgressState: ProgressState = loadState() ?? { games: {} }

const initalLevelProgressState: LevelProgressState = {code: "", completed: false, selections: []}

/** Add an empty skeleton with progress for the current level */
function addLevelProgress(state: ProgressState, action: PayloadAction<{game: string, world: string, level: number}>) {
  if (!state.games[action.payload.game]) {
    state.games[action.payload.game] = {}
  }
  if (!state.games[action.payload.game][action.payload.world]) {
    state.games[action.payload.game][action.payload.world] = {}
  }
  if (!state.games[action.payload.game][action.payload.world][action.payload.level]) {
    state.games[action.payload.game][action.payload.world][action.payload.level] = {...initalLevelProgressState}
  }
}

export const progressSlice = createSlice({
  name: 'progress',
  initialState: initialProgressState,
  reducers: {
    /** put edited code in the state and set completed to false */
    codeEdited(state: ProgressState, action: PayloadAction<{game: string, world: string, level: number, code: string}>) {
      addLevelProgress(state, action)
      state.games[action.payload.game][action.payload.world][action.payload.level].code = action.payload.code
      state.games[action.payload.game][action.payload.world][action.payload.level].completed = false
    },
    /** TODO: ? */
    changedSelection(state: ProgressState, action: PayloadAction<{game: string, world: string, level: number, selections: Selection[]}>) {
      addLevelProgress(state, action)
      state.games[action.payload.game][action.payload.world][action.payload.level].selections = action.payload.selections
    },
    /** mark level as completed */
    levelCompleted(state: ProgressState, action: PayloadAction<{game: string, world: string, level: number}>) {
      addLevelProgress(state, action)
      state.games[action.payload.game][action.payload.world][action.payload.level].completed = true
    },
    /** delete all progress for this game */
    deleteProgress(state: ProgressState, action: PayloadAction<{game: string}>) {
      state.games[action.payload.game] = {}
    },
    /** delete progress for this level */
    deleteLevelProgress(state: ProgressState, action: PayloadAction<{game: string, world: string, level: number}>) {
      addLevelProgress(state, action)
      state.games[action.payload.game][action.payload.world][action.payload.level] = initalLevelProgressState
    },
    /** load progress, e.g. from external import */
    loadProgress(state: ProgressState, action: PayloadAction<{game: string, data:GameProgressState}>) {
      console.debug(`setting data to:\n ${action.payload.data}`)
      state.games[action.payload.game] = action.payload.data
    },
  }
})

/** if the level does not exist, return default values */
export function selectLevel(game: string, world: string, level: number) {
  return (state) =>{
    if (!state.progress.games[game]) { return initalLevelProgressState }
    if (!state.progress.games[game][world]) { return initalLevelProgressState }
    if (!state.progress.games[game][world][level]) { return initalLevelProgressState }
    return state.progress.games[game][world][level]
  }
}

/** return the code of the current level */
export function selectCode(game: string, world: string, level: number) {
  return (state) => {
    return selectLevel(game, world, level)(state).code
  }
}

/** return the selections made in the current level */
export function selectSelections(game: string, world: string, level: number) {
  return (state) => {
    return selectLevel(game, world, level)(state).selections
  }
}

/** return whether the current level is clompleted */
export function selectCompleted(game: string, world: string, level: number) {
  return (state) => {
    return selectLevel(game, world, level)(state).completed
  }
}

/** return progress for the current game if it exists */
export function selectProgress(game: string) {
  return (state) => {
    return state.progress.games[game] ?? null
  }
}

/** Export actions to modify the progress */
export const { changedSelection, codeEdited, levelCompleted, deleteProgress,
  deleteLevelProgress, loadProgress } = progressSlice.actions
