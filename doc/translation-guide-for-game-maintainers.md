# Translations:  The game maintainer's point of view

This page provides an overview over our internationalisation ("i18n") setup for maintainers of games on our servers.  If you are interested in translating a specific game, you should refer to our [guide for translators](translation-guide-for-game-translators.md) instead.

## Workflow

The game server supports internationalisation ("i18n") using [lean-i18n](https://github.com/hhu-adam/lean-i18n) and [i18next](https://www.npmjs.com/package/i18next). The intended workflow is the following:

### 1. Preparation

- When you call `lake build` in your game, it should automatically create a template file `.i18n/en/Game.pot`. Alternatively you can call `lake exe i18n --template` to recreate it.  This template file is the only file that potential translators need in order to start working on a translation.

  For games written in a language different than English, you should set the correct source language (`sourceLang`) in `.i18n/config.json`. Afterwards, on `lake build` the template should appear under the chosen language, and can be translated (e.g. into English) as described above.  

- *Optional:*  You can simplify the work of translators by providing an additional glossary of mathematical terminology, lean concepts and other key words that appear in your game and which you anticipate will be difficult to translate (words that a machine translator would probably get wrong). Just make a list of such words in a text file, one word per line, and save it as `.i18n/en/glossary.csv`.

- *Optional:* We recommend maintaining a game-specific translation guide in addition to our generic [guide for translators](translation-guide-for-game-translators.md); see [Robo/Scribble](https://github.com/hhu-adam/Robo/blob/main/docs/TranslationGuide.md) for an example.

### 2. Translation

Share the files `Game.pot`, `glossary.csv` and any guidelines for translation with a potential translator.  If all goes well, they will eventually return a `.po`-file.

### 3. Review

We strongly recommend getting translations reviewed by a member of the lean community familiar with the language before publication.  This is to prevent both illegible machine translations as well as offensive or inappropriate language from appearing on the server.  We recommend the tool [Poedit](https://poedit.net/) for working with `.pot` and `.po` files.  Among other advantages, it allows you to specifically review a given range of sentences, e.g. 50–100 at a time, so you can distribute the review workload.

### 4. Publication
- Save the `.po` file with the translations to
  ```
  .i18n/{language}/Game.po
  ```
  where {language} is the ISO language code.
- Call `lake exe i18n --export-json` to create all `.json` files `.i18n/{language}/Game.json` which the server needs.
- Add the new translation (i.e. `.po` and `.json`, but not the `.mo` files) to your git repository, push your results, and [publish the game](publish_game.md).

- The server has a finite set of languages you can select.  If your language appears in the language list under `Menu` `>` `Preferences` in the game, you should now see your translations.

  If your language does not exist, please ask your translators to also [translate the game interface](translation-interface.md), or [open an issue](https://github.com/leanprover-community/lean4game/issues) requesting this new language.

## Alternative: avoiding `.po` files (not recommended)

Note: This workflow is subject to change, and it might be that in future the server can directly read `.po` files. Until then, there is also an alternative workflow you might choose:

0. Add `useJson: true` to `.i18n/config.json`
1. `lake build` or `lake exe i18n --template` will now create a Json instead: `.i18n/en/Game.json`.
2. Add translations to a copy of this Json an save it as `.i18n/{language}/Game.json`
