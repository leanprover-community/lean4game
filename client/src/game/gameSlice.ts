import { createSlice, PayloadAction } from '@reduxjs/toolkit'
import { LeanClient } from 'lean4web/client/src/editor/leanclient'
import { Connection } from '../connection'
import type { RootState } from '../store'

interface GameState {
  title: null|string,
  introduction: null|string,
  worlds: null|{nodes: string[], edges: string[][2]},
  authors: null|string[],
  conclusion: null|string,
}

const initialState : GameState = {
  title: null,
  introduction: null,
  worlds: null,
  authors: null,
  conclusion: null,
}

export const gameSlice = createSlice({
  name: 'game',
  initialState,
  reducers: {
    loadedGame: (state, action: PayloadAction<any>) => {
      state.title = action.payload.title
      state.introduction = action.payload.introduction
      state.worlds = action.payload.worlds
      state.authors = action.payload.authors
      state.conclusion = action.payload.conclusion
    },
  },
})

export const { loadedGame } = gameSlice.actions


export const fetchGame = (dispatch, getState, extraArgument) => {
  const connection : Connection = extraArgument.connection
  connection.whenLeanClientStarted(() => {
    connection.getLeanClient().sendRequest("info", {}).then((res) =>{
      dispatch(loadedGame(res))
    })
  })
}

export default gameSlice.reducer
