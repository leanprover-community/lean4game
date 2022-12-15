import { createSlice } from '@reduxjs/toolkit'
import type { PayloadAction } from '@reduxjs/toolkit'

interface ProgressState {
  code: {[world: string]: {[level: number]: string}}
}

const initialState = { code: {} } as ProgressState

export const progressSlice = createSlice({
  name: 'progress',
  initialState,
  reducers: {
    codeEdited(state, action: PayloadAction<{world: string, level: number, code: string}>) {
      if (!state.code[action.payload.world]) {
        state.code[action.payload.world] = {}
      }
      state.code[action.payload.world][action.payload.level] = action.payload.code
    },
  }
})

export function selectCode(world: string, level: number) {
  return (state) => {
    if (!state.progress.code[world]) { return undefined }
    return state.progress.code[world][level];
  }
}

export const { codeEdited } = progressSlice.actions
