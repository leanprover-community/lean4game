# Translation of the game interface

The interface can be translated to various languages. For adding a translation, one needs to do the following:

1. In `client/src/config.json`, add your new language. The "iso" key is the ISO language code, i.e. it should be accepted by "i18next" and "GNU gettext"; the "flag" key is once accepted by [react-country-flag](https://www.npmjs.com/package/react-country-flag).
2. Run `npm run translate`. This should create a new file `client/public/locales/{language}/translation.json`. (Alternatively, you can copy-paste `client/public/locales/en/translation.json`.)
3. Add all translations.
4. Commit the changes you made to `config.json` together with the new `translation.json`.

For translating games, please see the dedicated pages for [game maintainers](translation-guide-for-game-maintainers.md) and [game translators](translation-guide-for-game-translators.md).
