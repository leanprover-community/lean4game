import GameServer.EnvExtensions

open Lean GameServer

private def oldSettingsJson := Json.mkObj [
  ("unbundleHyps", toJson false)
]

private def emptyTranslationsEnabledJson := Json.mkObj [
  ("allowEmptyTranslations", toJson true),
  ("fallbackLanguage", toJson "de"),
  ("hideMissingTranslations", toJson true),
  ("unbundleHyps", toJson false)
]

private def invalidSettingsJson := Json.mkObj [
  ("allowEmptyTranslations", toJson "yes")
]

#guard match fromJson? (α := Game.Settings) oldSettingsJson with
  | .ok settings => !settings.allowEmptyTranslations && settings.fallbackLanguage == "en" &&
      !settings.hideMissingTranslations && !settings.unbundleHyps
  | .error _ => false

#guard match fromJson? (α := Game.Settings) emptyTranslationsEnabledJson with
  | .ok settings => settings.allowEmptyTranslations && settings.fallbackLanguage == "de" &&
      settings.hideMissingTranslations && !settings.unbundleHyps
  | .error _ => false

#guard match fromJson? (α := Game.Settings) invalidSettingsJson with
  | .ok _ => false
  | .error _ => true
