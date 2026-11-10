import GameApi.EnvExtensions
import I18n

/-!
Commands to define auxilary information about the game, which might be used
for display in the frontend but has not influence on the game's content.
-/

namespace GameServer

open Lean

/-- A list of games that should be played before this one. Example `Prerequisites "NNG" "STG"`. -/
elab "Prerequisites" t:str* : command => do
  modifyCurGame fun game => pure {game with
    tile := {game.tile with prerequisites := t.map (·.getString) |>.toList}}

/-- Short caption for the game (1 sentence) -/
elab "CaptionShort" t:str : command => do
  let caption ← t.getString.translate
  modifyCurGame fun game => pure {game with
    tile := {game.tile with short := caption}}

/-- More detailed description what the game is about (2-4 sentences). -/
elab "CaptionLong" t:str : command => do
  let caption ← t.getString.translate
  modifyCurGame fun game => pure {game with
    tile := {game.tile with long := caption}}

/--
Whether `s` looks like a language code, e.g. `en`, `pt-BR` or `zh-Hans`: two or three
lowercase letters, optionally followed by subtags of 2–8 letters or digits, each after a `-`.
It is not checked that the code exists.
-/
def isLanguageCode (s : String) : Bool :=
  match s.splitOn "-" with
  | [] => false
  | lang :: subtags =>
    (lang.length == 2 ∨ lang.length == 3) ∧ lang.all (fun c => c.isLower) ∧
    subtags.all fun tag => 2 ≤ tag.length ∧ tag.length ≤ 8 ∧ tag.all Char.isAlphanum

/-- A list of Languages the game is translated to. For example `Languages "de" "en"`.

The keys are ISO language codes, e.g. `en` or `pt-BR`.
 -/
elab "Languages" t:str* : command => do
  for lang in t do
    unless isLanguageCode lang.getString do
      logWarningAt lang m!"'{lang.getString}' is not a language code. Use ISO codes like \"en\" or \"pt-BR\" instead."
  modifyCurGame fun game => pure {game with
    tile := {game.tile with languages := t.map (·.getString) |>.toList}}

/-- The Image of the game (optional). TODO: Not implemented -/
elab "CoverImage" t:str : command => do
  let file := t.getString
  if not <| ← System.FilePath.pathExists file then
    logWarningAt t s!"Make sure the cover image '{file}' exists."
  if not <| file.startsWith "images/" then
    logWarningAt t s!"The file name should start with `images/`. Make sure all images are in that folder."

  modifyCurGame fun game => pure {game with
    tile := {game.tile with image := file}}

/-- Define the info of the current game. Used for e.g. credits -/
elab "Info" t:str : command => do
  let info ← t.getString.translate
  match ← getCurLayer with
  | .Level =>
    logError "Can't use `Info` in a level!"
    pure ()
  | .World =>
    logError "Can't use `Info` in a world"
    pure ()
  | .Game => modifyCurGame  fun game => pure {game with info := info}

-- Note: the syntax to add multiple is `(&"anotherOption" <|> &"unbundleHyps")`
syntax settingsArg := atomic(" (" (&"unbundleHyps") " := " withoutPosition(term) ")")

open Elab in
/--
Settings to customise the game appearance. Usage `Settings (setting1 := val1) (setting2 := val2)`.
Valid settings are:

* (unbundleHyps := false)
 -/
elab "Settings " args:settingsArg* : command => do
  let mut settings: Game.Settings := default
  for arg in args do
    match arg with
    | `(settingsArg| (unbundleHyps := true)) => settings := { settings with unbundleHyps := true }
    | `(settingsArg| (unbundleHyps := false)) => settings := { unbundleHyps := false }
    | _ => throwUnsupportedSyntax
  modifyCurGame (pure { · with settings := settings })
