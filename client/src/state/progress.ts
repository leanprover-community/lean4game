import { createSlice } from '@reduxjs/toolkit'
import type { PayloadAction } from '@reduxjs/toolkit'
import { loadState } from "./localStorage";

interface ProgressState {
  level: {[game: string]: {[world: string]: {[level: number]: LevelProgressState}}}
}
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

const initialProgressState = loadState() ?? { level: {} } as ProgressState
const initalLevelProgressState = {code: "", completed: false} as LevelProgressState

function addLevelProgress(state, action: PayloadAction<{game: string, world: string, level: number}>) {
  if (!state.level[action.payload.game]) {
    state.level[action.payload.game] = {}
  }
  if (!state.level[action.payload.game][action.payload.world]) {
    state.level[action.payload.game][action.payload.world] = {}
  }
  if (!state.level[action.payload.game][action.payload.world][action.payload.level]) {
    state.level[action.payload.game][action.payload.world][action.payload.level] = {...initalLevelProgressState}
  }
}

export const progressSlice = createSlice({
  name: 'progress',
  initialState: initialProgressState,
  reducers: {
    codeEdited(state, action: PayloadAction<{game: string, world: string, level: number, code: string}>) {
      addLevelProgress(state, action)
      state.level[action.payload.game][action.payload.world][action.payload.level].code = action.payload.code
      state.level[action.payload.game][action.payload.world][action.payload.level].completed = false
    },
    changedSelection(state, action: PayloadAction<{game: string, world: string, level: number, selections: Selection[]}>) {
      addLevelProgress(state, action)
      state.level[action.payload.game][action.payload.world][action.payload.level].selections = action.payload.selections
    },
    levelCompleted(state, action: PayloadAction<{game: string, world: string, level: number}>) {
      addLevelProgress(state, action)
      state.level[action.payload.game][action.payload.world][action.payload.level].completed = true
    },
  }
})

export function selectLevel(game: string, world: string, level: number) {
  return (state) =>{
    if (!state.progress.level[game]) { return initalLevelProgressState }
    if (!state.progress.level[game][world]) { return initalLevelProgressState }
    if (!state.progress.level[game][world][level]) { return initalLevelProgressState }
    return state.progress.level[game][world][level]
  }
}

export function selectCode(game: string, world: string, level: number) {
  return (state) => {
    return selectLevel(game, world, level)(state).code
  }
}

export function selectSelections(game: string, world: string, level: number) {
  return (state) => {
    return selectLevel(game, world, level)(state).selections
  }
}

export function selectCompleted(game: string, world: string, level: number) {
  return (state) => {
    return selectLevel(game, world, level)(state).completed
  }
}

export function selectProgress() {
  return (state) => {
    return state.progress
  }
}

export const { changedSelection, codeEdited, levelCompleted } = progressSlice.actions
