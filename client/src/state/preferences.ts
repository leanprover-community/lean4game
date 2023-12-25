import { createSlice } from "@reduxjs/toolkit";

import { loadPreferences } from "./local_storage";

interface PreferencesState {
  mobile: boolean;
  lockMobile: boolean;
}

export function getWindowDimensions() {
  const {innerWidth: width, innerHeight: height } = window
  return {width, height}
}

const { width } = getWindowDimensions()

export const AUTO_SWITCH_THRESHOLD = 800

const initialState: PreferencesState = loadPreferences() ?? {
    mobile: width < AUTO_SWITCH_THRESHOLD,
    lockMobile: false
}

export const preferencesSlice = createSlice({
  name: "preferences",
  initialState,
  reducers: {
    setMobile: (state, action) => {
      state.mobile = action.payload;
    },
    setLockMobile: (state, action) => {
      state.lockMobile = action.payload;
    },
  },
});

export const { setMobile, setLockMobile } = preferencesSlice.actions;
