/**
 * @fileOverview configure the store and save the state periodically to the browser storage
*/
import { configureStore } from '@reduxjs/toolkit';
import { debounce } from "debounce";

import { connection } from '../connection'
import { apiSlice } from './api'
import { progressSlice } from './progress'
import { preferencesSlice } from "./preferences"
import { saveState, savePreferences, removePreferences} from "./local_storage";


export const store = configureStore({
  reducer: {
    [apiSlice.reducerPath]: apiSlice.reducer,
    [progressSlice.name]: progressSlice.reducer,
    [preferencesSlice.name]: preferencesSlice.reducer,
  },
  // Make connection available in thunks:
  middleware: getDefaultMiddleware =>
    getDefaultMiddleware().concat(apiSlice.middleware),
});

/**
 * Save progress in local storage once each 800ms.
 * This is for better performance when multiple changes occur in a short time
 */
store.subscribe(
  debounce(() => {
    saveState(store.getState()[progressSlice.name]);

    const preferencesState= store.getState()[preferencesSlice.name]
    preferencesState.isSavePreferences ? savePreferences(preferencesState) : removePreferences()
  }, 800)
);

// Infer the `RootState` and `AppDispatch` types from the store itself
export type RootState = ReturnType<typeof store.getState>
// Inferred type: {posts: PostsState, comments: CommentsState, users: UsersState}
export type AppDispatch = typeof store.dispatch
