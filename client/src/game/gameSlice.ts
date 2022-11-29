import { createSlice, PayloadAction } from '@reduxjs/toolkit'
import { LeanClient } from 'lean4web/client/src/editor/leanclient'
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

// TODO: Move this into LeanClient?
/** Call `callback` when the leanClient has started. If not already started, start it. */
const whenLeanClientStarted = (leanClient, callback) => {
  if (leanClient.isRunning()) {
    callback()
  } else {
    if (!leanClient.isStarted()) {
      leanClient.start()
    }
    leanClient.restarted(callback)
  }
}

export const fetchGame = (dispatch, getState, extraArgument) => {
  const leanClient : LeanClient = extraArgument.leanClient
  whenLeanClientStarted(leanClient, () => {
    leanClient.sendRequest("info", {}).then((res) =>{
      dispatch(loadedGame(res))
    })
  })
}

export default gameSlice.reducer
