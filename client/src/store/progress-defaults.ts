import { LevelProgress, WorldProgress } from "./progress-types"

export const createDefaultWorldProgress = (): WorldProgress => ({
  readIntro: false,
} as WorldProgress)

export const createDefaultLevelProgress = (): LevelProgress => ({
  code: "",
  selections: [],
  completed: false,
  help: [],
})
