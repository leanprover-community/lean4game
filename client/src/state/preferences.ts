import { createSlice } from "@reduxjs/toolkit";

import { loadPreferences, removePreferences, savePreferences } from "./local_storage";

export interface PreferencesState {
  layout: "mobile" | "auto" | "desktop";
  isSavePreferences: boolean;
}

export function getWindowDimensions() {
  const {innerWidth: width, innerHeight: height } = window
  return {width, height}
}

export const AUTO_SWITCH_THRESHOLD = 800

const initialState: PreferencesState = loadPreferences() ??{
    layout: "auto",
    isSavePreferences: false
}

export const preferencesSlice = createSlice({
  name: "preferences",
  initialState,
  reducers: {
    setLayout: (state, action) => {
      state.layout = action.payload;
    },
    setisSavePreferences: (state, action) => {
      state.isSavePreferences = action.payload;
    },
  },
});

export const { setLayout, setisSavePreferences } = preferencesSlice.actions;
