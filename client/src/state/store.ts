import { configureStore } from '@reduxjs/toolkit';
import { connection } from '../connection'
import thunkMiddleware from 'redux-thunk'
import { apiSlice } from './api'
import { progressSlice } from './progress'


export const store = configureStore({
  reducer: {
    [apiSlice.reducerPath]: apiSlice.reducer,
    [progressSlice.name]: progressSlice.reducer,
  },
  middleware: getDefaultMiddleware =>
    getDefaultMiddleware({
      thunk: {
        extraArgument: { connection }
      }
    }).concat(apiSlice.middleware),
});

// Infer the `RootState` and `AppDispatch` types from the store itself
export type RootState = ReturnType<typeof store.getState>
// Inferred type: {posts: PostsState, comments: CommentsState, users: UsersState}
export type AppDispatch = typeof store.dispatch
