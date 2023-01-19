import { createSlice } from '@reduxjs/toolkit'
import type { PayloadAction } from '@reduxjs/toolkit'
import { loadState } from "./localStorage";

interface ProgressState {
  level: {[world: string]: {[level: number]: LevelProgressState}}
}

interface LevelProgressState {
  code: string,
  completed: boolean
}

const initialProgressState = loadState() ?? { level: {} } as ProgressState
const initalLevelProgressState = {code: "", completed: false} as LevelProgressState

function addLevelProgress(state, action: PayloadAction<{world: string, level: number}>) {
  if (!state.level[action.payload.world]) {
    state.level[action.payload.world] = {}
  }
  if (!state.level[action.payload.world][action.payload.level]) {
    state.level[action.payload.world][action.payload.level] = {...initalLevelProgressState}
  }
}

export const progressSlice = createSlice({
  name: 'progress',
  initialState: initialProgressState,
  reducers: {
    codeEdited(state, action: PayloadAction<{world: string, level: number, code: string}>) {
      addLevelProgress(state, action)
      state.level[action.payload.world][action.payload.level].code = action.payload.code
      state.level[action.payload.world][action.payload.level].completed = false
    },
    levelCompleted(state, action: PayloadAction<{world: string, level: number}>) {
      addLevelProgress(state, action)
      state.level[action.payload.world][action.payload.level].completed = true
    },
  }
})

export function selectLevel(world: string, level: number) {
  return (state) =>{
    if (!state.progress.level[world]) { return initalLevelProgressState }
    if (!state.progress.level[world][level]) { return initalLevelProgressState }
    return state.progress.level[world][level]
  }
}

export function selectCode(world: string, level: number) {
  return (state) => {
    return selectLevel(world, level)(state).code
  }
}

export function selectCompleted(world: string, level: number) {
  return (state) => {
    return selectLevel(world, level)(state).completed
  }
}

export function selectProgress() {
  return (state) => {
    return state.progress
  }
}

export const { codeEdited, levelCompleted } = progressSlice.actions
