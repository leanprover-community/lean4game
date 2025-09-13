import { createSlice } from "@reduxjs/toolkit";

import { loadPreferences, removePreferences, savePreferences } from "./local_storage";

export interface PreferencesState {
  layout: "mobile" | "auto" | "desktop";
  isSavePreferences: boolean;
  language: string;
  isSuggestionsMobileMode: boolean;
}

export function getWindowDimensions() {
  const {innerWidth: width, innerHeight: height } = window
  return {width, height}
}

export const AUTO_SWITCH_THRESHOLD = 800

const initialState: PreferencesState = loadPreferences() ??{
    layout: "auto",
    isSavePreferences: false,
    language: import.meta.env.VITE_CLIENT_DEFAULT_LANGUAGE || "en",
    isSuggestionsMobileMode: 'ontouchstart' in document.documentElement,
};

export const preferencesSlice = createSlice({
  name: "preferences",
  initialState,
  reducers: {
    setLayout: (state, action) => {
      state.layout = action.payload;
    },
    setIsSavePreferences: (state, action) => {
      state.isSavePreferences = action.payload;
    },
    setLanguage: (state, action) => {
      state.language = action.payload;
    },
    setIsSuggestionsMobileMode: (state, action) => {
      state.isSuggestionsMobileMode = action.payload;
    },
  },
});

export const { setLayout, setIsSavePreferences, setLanguage, setIsSuggestionsMobileMode } = preferencesSlice.actions;
