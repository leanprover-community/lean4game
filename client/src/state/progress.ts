/**
 * @fileOverview Defines the user progress which is loaded from the browser store and kept
 */
import { createSlice } from '@reduxjs/toolkit'
import type { PayloadAction } from '@reduxjs/toolkit'
import { loadState } from "./local_storage";
import { WorkDoneProgressBegin } from 'vscode-languageserver-protocol';

interface Selection {
  selectionStartLineNumber: number,
  selectionStartColumn: number,
  positionLineNumber: number
  positionColumn: number
}
interface LevelProgressState {
  code: string,
  selections: Selection[],
  completed: boolean,
  help: number[], // A set of rows where hidden hints have been displayed
}
interface WorldProgressState {
  [world: string] : {[level: number]: LevelProgressState, readIntro: boolean},
}

export interface GameProgressState {
  inventory: string[],
  difficulty: number,
  readIntro: boolean,
  data: WorldProgressState,
  typewriterMode?: boolean
}

/**
 * Currently we have three difficulties:
 *
 *   | lock tactics | lock levels |
 * --|--------------|-------------|
 * 0 |      no      |      no     |
 * 1 |     yes      |      no     |
 * 2 |     yes      |     yes     |
 */
const DEFAULT_DIFFICULTY = 2

/** The progress made on all lean4-games */
interface ProgressState {
  games: {[game: string]: GameProgressState}
}

const initialProgressState: ProgressState = loadState() ?? { games: {} }

// TODO: There was some weird unreproducible bug with removing `as LevelProgressState` here...
const initalLevelProgressState: LevelProgressState = {code: "", completed: false, selections: [], help: []}

/** Add an empty skeleton with progress for the current game */
function addGameProgress (state: ProgressState, action: PayloadAction<{game: string}>) {
  if (!state.games[action.payload.game.toLowerCase()]) {
    state.games[action.payload.game.toLowerCase()] = {inventory: [], readIntro: false, data: {}, difficulty: DEFAULT_DIFFICULTY}
  }
  if (!state.games[action.payload.game.toLowerCase()].data) {
    state.games[action.payload.game.toLowerCase()].data = {}
  }
}

function addWorldProgress(state: ProgressState, action: PayloadAction<{game: string, world: string}>) {
  addGameProgress(state, action)
  if (!state.games[action.payload.game.toLowerCase()].data[action.payload.world]) {
    state.games[action.payload.game.toLowerCase()].data[action.payload.world] = {readIntro: false}
  }
}

/** Add an empty skeleton with progress for the current level */
function addLevelProgress(state: ProgressState, action: PayloadAction<{game: string, world: string, level: number}>) {
  addGameProgress(state, action)
  addWorldProgress(state, action)
  if (!state.games[action.payload.game.toLowerCase()].data[action.payload.world][action.payload.level]) {
    state.games[action.payload.game.toLowerCase()].data[action.payload.world][action.payload.level] = {...initalLevelProgressState}
  }
}

export const progressSlice = createSlice({
  name: 'progress',
  initialState: initialProgressState,
  reducers: {
    /** put edited code in the state and set completed to false */
    codeEdited(state: ProgressState, action: PayloadAction<{game: string, world: string, level: number, code: string}>) {
      addLevelProgress(state, action)
      state.games[action.payload.game.toLowerCase()].data[action.payload.world][action.payload.level].code = action.payload.code
      // state.games[action.payload.game.toLowerCase()].data[action.payload.world][action.payload.level].completed = false
    },
    /** TODO: docstring */
    changedSelection(state: ProgressState, action: PayloadAction<{game: string, world: string, level: number, selections: Selection[]}>) {
      addLevelProgress(state, action)
      state.games[action.payload.game.toLowerCase()].data[action.payload.world][action.payload.level].selections = action.payload.selections
    },
    /** mark level as completed */
    levelCompleted(state: ProgressState, action: PayloadAction<{game: string, world: string, level: number}>) {
      addLevelProgress(state, action)
      state.games[action.payload.game.toLowerCase()].data[action.payload.world][action.payload.level].completed = true
    },
    /** Set the list of rows where help is displayed */
    helpEdited(state: ProgressState, action: PayloadAction<{game: string, world: string, level: number, help: number[]}>) {
      addLevelProgress(state, action)
      console.debug(`!setting help to: ${action.payload.help}`)
      state.games[action.payload.game.toLowerCase()].data[action.payload.world][action.payload.level].help = action.payload.help
    },
    /** delete all progress for this game */
    deleteProgress(state: ProgressState, action: PayloadAction<{game: string}>) {
      state.games[action.payload.game.toLowerCase()] = {inventory: [], data: {}, readIntro: false, difficulty: DEFAULT_DIFFICULTY}
    },
    /** delete progress for this level */
    deleteLevelProgress(state: ProgressState, action: PayloadAction<{game: string, world: string, level: number}>) {
      addLevelProgress(state, action)
      state.games[action.payload.game.toLowerCase()].data[action.payload.world][action.payload.level] = initalLevelProgressState
    },
    /** load progress, e.g. from external import */
    loadProgress(state: ProgressState, action: PayloadAction<{game: string, data:GameProgressState}>) {
      console.debug(`setting data to:\n ${action.payload.data}`)
      state.games[action.payload.game.toLowerCase()] = action.payload.data
    },
    /** set the current inventory */
    changedInventory(state: ProgressState, action: PayloadAction<{game: string, inventory: string[]}>) {
      addGameProgress(state, action)
      state.games[action.payload.game.toLowerCase()].inventory = action.payload.inventory
    },
    /** set the difficulty */
    changedDifficulty(state: ProgressState, action: PayloadAction<{game: string, difficulty: number}>) {
      addGameProgress(state, action)
      state.games[action.payload.game.toLowerCase()].difficulty = action.payload.difficulty
    },
    /** set the difficulty */
    changedReadIntro(state: ProgressState, action: PayloadAction<{game: string, world: string, readIntro: boolean}>) {
      addWorldProgress(state, action)
      if (action.payload.world) {
        state.games[action.payload.game.toLowerCase()].data[action.payload.world].readIntro = action.payload.readIntro
      } else {
        state.games[action.payload.game.toLowerCase()].readIntro = action.payload.readIntro
      }
    },
    /** set the typewriter mode */
    changeTypewriterMode(state: ProgressState, action: PayloadAction<{game: string, typewriterMode: boolean}>) {
      addGameProgress(state, action)
      state.games[action.payload.game.toLowerCase()].typewriterMode = action.payload.typewriterMode
    }
  }
})

/** if the level does not exist, return default values */
export function selectLevel(game: string, world: string, level: number) {
  return (state) => {
    if (!state.progress.games[game?.toLowerCase()]) { return initalLevelProgressState }
    if (!state.progress.games[game?.toLowerCase()]?.data[world]) { return initalLevelProgressState }
    if (!state.progress.games[game?.toLowerCase()]?.data[world][level]) { return initalLevelProgressState }
    return state.progress.games[game?.toLowerCase()]?.data[world][level]
  }
}

/** return the code of the current level */
export function selectCode(game: string, world: string, level: number) {
  return (state) => {
    return selectLevel(game?.toLowerCase(), world, level)(state).code
  }
}

/** return the current inventory */
export function selectInventory(game: string) {
  return (state) => {
    if (!state.progress.games[game?.toLowerCase()]) { return [] }
    return state.progress.games[game?.toLowerCase()]?.inventory
  }
}

/** return the code of the current level */
export function selectHelp(game: string, world: string, level: number) {
  return (state) => {
    return selectLevel(game?.toLowerCase(), world, level)(state).help
  }
}

/** return the selections made in the current level */
export function selectSelections(game: string, world: string, level: number) {
  return (state) => {
    return selectLevel(game?.toLowerCase(), world, level)(state).selections
  }
}

/** return whether the current level is clompleted */
export function selectCompleted(game: string, world: string, level: number) {
  return (state) => {
    return selectLevel(game?.toLowerCase(), world, level)(state).completed
  }
}

/** return progress for the current game if it exists */
export function selectProgress(game: string) {
  return (state) => {
    return state.progress.games[game?.toLowerCase()] ?? null
  }
}

/** return difficulty for the current game if it exists */
export function selectDifficulty(game: string) {
  return (state) => {
    return state.progress.games[game?.toLowerCase()]?.difficulty ?? DEFAULT_DIFFICULTY
  }
}

/** return whether the intro has been read */
export function selectReadIntro(game: string, worldId: string) {
  return (state) => {
    if (worldId) {
      return state.progress.games[game?.toLowerCase()]?.data[worldId]?.readIntro
    }
    return state.progress.games[game?.toLowerCase()]?.readIntro
  }
}

/** return typewriter mode for the current game if it exists */
export function selectTypewriterMode(game: string) {
  return (state) => {
    return state.progress.games[game?.toLowerCase()]?.typewriterMode ?? true
  }
}

/** Export actions to modify the progress */
export const { changedSelection, codeEdited, levelCompleted, deleteProgress,
  deleteLevelProgress, loadProgress, helpEdited, changedInventory, changedReadIntro,
  changedDifficulty, changeTypewriterMode} = progressSlice.actions
