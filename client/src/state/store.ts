import { configureStore } from '@reduxjs/toolkit';
import { debounce } from "debounce";

import { connection } from '../connection'
import { apiSlice } from './api'
import { progressSlice } from './progress'
import { saveState } from "./local_storage";


export const store = configureStore({
  reducer: {
    [apiSlice.reducerPath]: apiSlice.reducer,
    [progressSlice.name]: progressSlice.reducer,
  },
  // Make connection available in thunks:
  middleware: getDefaultMiddleware =>
    getDefaultMiddleware({
      thunk: {
        extraArgument: { connection }
      }
    }).concat(apiSlice.middleware),
});

// Save progress in local storage
store.subscribe(
  // we use debounce to save the state once each 800ms
  // for better performances in case multiple changes occur in a short time
  debounce(() => {
    saveState(store.getState()[progressSlice.name]);
  }, 800)
);

// Infer the `RootState` and `AppDispatch` types from the store itself
export type RootState = ReturnType<typeof store.getState>
// Inferred type: {posts: PostsState, comments: CommentsState, users: UsersState}
export type AppDispatch = typeof store.dispatch
