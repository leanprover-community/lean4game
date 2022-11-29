import { configureStore } from '@reduxjs/toolkit';
import gameReducer from './game/gameSlice';
import { leanClient } from './connection'
import thunkMiddleware from 'redux-thunk'


const thunkMiddlewareWithArg = thunkMiddleware.withExtraArgument({ leanClient })

export const store = configureStore({
  reducer: {
    game: gameReducer,
  },
  middleware: getDefaultMiddleware =>
    getDefaultMiddleware({
      thunk: {
        extraArgument: { leanClient }
      }
    })
});

// Infer the `RootState` and `AppDispatch` types from the store itself
export type RootState = ReturnType<typeof store.getState>
// Inferred type: {posts: PostsState, comments: CommentsState, users: UsersState}
export type AppDispatch = typeof store.dispatch
