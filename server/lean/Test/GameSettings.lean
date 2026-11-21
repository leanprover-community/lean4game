import GameApi

open Lean Elab Command GameServer

/-! The `Settings` command of a game -/

Game "TestGameSettings"

Settings (unbundleHyps := true) (allowEmptyTranslations := true) (printGoalText := true)

#eval show CommandElabM Unit from do
  let settings := (← getCurGame).settings
  unless settings.unbundleHyps && settings.allowEmptyTranslations && settings.printGoalText do
    throwError "all settings should be enabled"

-- setting one to `false` keeps the others
Settings (allowEmptyTranslations := true) (printGoalText := true) (unbundleHyps := false)

#eval show CommandElabM Unit from do
  let settings := (← getCurGame).settings
  unless !settings.unbundleHyps && settings.allowEmptyTranslations && settings.printGoalText do
    throwError "only `unbundleHyps` should be disabled"
