# Translation

The game server supports internationalisation ("i18n") using [lean-i18n](https://github.com/hhu-adam/lean-i18n) and [i18next](https://www.npmjs.com/package/i18next).

1. When you call `lake build` in your game, it should automatically create a template file `.i18n/en/Game.pot`. Alternatively you can call `lake exe i18n --template` to recreate it.
2. Open the file `Game.pot` (the "t" stands for "template") with [Poedit](https://poedit.net/) (or a similar software) and translate all strings. Save your work as `.i18n/{language}/Game.po`.
4. Call `lake exe i18n --export-json` to create all Json files `.i18n/{language}/Game.json` which the server needs.
5. Add your translations (i.e. `.po` and `.json`, but not the `.mo` files) and push your results, and [publish the game](doc/publish_game.md).

If you choose the correct language in the "Preferences" of the game, you should see your translations.

## Alternative: avoiding .po

Note: This workflow is subject to change, and it might be that in future the server can directly read `.po` files. Until then, there is also an alternative workflow you might choose:

0. Add `useJson: true` to `.i18n/config.json`
1. `lake build` or `lake exe i18n --template` will now create a Json instead: `.i18n/en/Game.json`.
2. Add translations to a copy of this Json an save it as `.i18n/{language}/Game.json`

## non-English games

For games not originally written in English, you should set the correct source language (`sourceLang`) in `.i18n/config.json`. Now the template should appear under the chosen language.

## New languages

The server has a set number of languages one can select.
If your game has been translated to a language not selectable, [open an issue at lean4game](https://github.com/leanprover-community/lean4game/issues) requesting this new language.
Or, even better, create a PR to translate the [server interface](https://github.com/leanprover-community/lean4game/tree/main/client/public/locales) into that new language.
