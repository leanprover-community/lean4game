import GameApi

open Lean Elab Command GameServer

/-! The `Settings` command of a game -/

Game "TestGameSettings"

Settings (unbundleHyps := true) (allowEmptyTranslations := true)

#eval show CommandElabM Unit from do
  let settings := (← getCurGame).settings
  unless settings.unbundleHyps && settings.allowEmptyTranslations do
    throwError "both settings should be enabled"

-- setting one to `false` keeps the other
Settings (allowEmptyTranslations := true) (unbundleHyps := false)

#eval show CommandElabM Unit from do
  let settings := (← getCurGame).settings
  unless !settings.unbundleHyps && settings.allowEmptyTranslations do
    throwError "only `allowEmptyTranslations` should be enabled"
