# Translation

The game server supports internationalisation ("i18n") using [lean-i18n](https://github.com/hhu-adam/lean-i18n) and [i18next](https://www.npmjs.com/package/i18next).

The intended workflow currently is the following:

1. When you call `lake build` in your game, it should automatically create a template file `.i18n/en/Game.pot`. Alternatively you can call `lake exe i18n --template` to recreate it.
2. Open the file `Game.pot` (the "t" stands for "template") with [Poedit](https://poedit.net/) (or a similar software) and translate all strings. Save your work as `.i18n/{language}/Game.po`.
4. Call `lake exe i18n --export-json` to create all Json files `.i18n/{language}/Game.json` which the server needs.
5. Add your translations (i.e. `.po` and `.json`, but not the `.mo` files) and push your results, and [publish the game](publish_game.md).

If you choose the correct language in the "Preferences" of the game, you should see your translations.

## Alternative: avoiding .po

Note: This workflow is subject to change, and it might be that in future the server can directly read `.po` files. Until then, there is also an alternative workflow you might choose:

0. Add `useJson: true` to `.i18n/config.json`
1. `lake build` or `lake exe i18n --template` will now create a Json instead: `.i18n/en/Game.json`.
2. Add translations to a copy of this Json an save it as `.i18n/{language}/Game.json`

## Non-English games

For games written in a language different than English, you should set the correct source language (`sourceLang`) in `.i18n/config.json`. Afterwards, on `lake build` the template should appear under the chosen language, and can be translated (e.g. into English) as described above.

## New languages

The server has a set number of languages one can select.
If your game has been translated to a language not selectable, [open an issue at lean4game](https://github.com/leanprover-community/lean4game/issues) requesting this new language.
Or, even better, create a PR to translate the [server interface](https://github.com/leanprover-community/lean4game/tree/main/client/public/locales) into that new language.

## Review

If you send your translation for review to person who don't know about Lean4Game here followwing recomendations based on experience:

1. Explicitly specify what file to review. Sometimes people go to JSON file in presence of PO file, even if that's in PR description
2. Make sure that you let your reviewer know that formatting should be preserved during translation. That's not obvious. For example `` ` `` maye be translated as `"`, That's unlikely what you want to miss. Reviewer should be aware about such mistakes coming from automatic translation tools.
3. Let know reviewer about list of words which can be incorrectly interpreted. That's usually tactics - `intro`, `induction`, `case`.
4. Explicitly suggest use [POEdit](https://poedit.net/) or other translation tool for PO manipulation, since that allow you speak about sentence ranges, and ask for review for example translations in range from 200-299. That allow you to recruit multiple pair of eyes, if people are busy. Also it's much easier find time to review 50-100 sentences in one go. Less likely to have fatigue from that activity.
