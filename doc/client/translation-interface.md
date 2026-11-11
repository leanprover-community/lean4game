# Translation of the game interface

The interface can be translated to various languages. For adding a translation, one needs to do the following:

1. In `client/src/config.json`, add your new language. The "iso" key is the ISO language code, i.e. it should be accepted by "i18next" and "GNU gettext"; the "flag" key is once accepted by [react-country-flag](https://www.npmjs.com/package/react-country-flag).
2. Run `npm run translate`. This should create a new file `client/public/locales/{language}/translation.json`. (Alternatively, you can copy-paste `client/public/locales/en/translation.json`.)
3. Add all translations.
4. Commit the changes you made to `config.json` together with the new `translation.json`.

For translating games, please see the dedicated pages for [game maintainers](../game/translation-guide-for-game-maintainers.md) and [game translators](../game/translation-guide-for-game-translators.md).

## New way

The translations of the interface are TypeScript files in `client/src/translations/`, one per
language, e.g. `de.ts`. English, `en.ts`, is the reference: all keys are defined there, and
missing translations fall back to it.

### Adding a language

1. In `client/src/config.json`, add your new language. The `iso` key is the ISO language code,
   i.e. it should be accepted by i18next and GNU gettext; `name` is the name of the language in
   that language; the optional `flag` key is a country code accepted by
   [react-country-flag](https://www.npmjs.com/package/react-country-flag).
2. Create the file `client/src/translations/{language}.ts` like the existing ones, e.g. for
   German:

   ```ts
   import type { DeepPartialTranslation } from '../utils/DeepPartialTranslation'
   import type { en } from './en'

   export const de: DeepPartialTranslation<typeof en> = {
     // the same structure as in `en.ts`
   }
   ```

   The type checks that every key of the translation file is also present in`en.ts`, but
   missing keys are allowed.

3. In `client/src/i18n.ts`, import the new translation and add it to `resources`.
4. Add the translations, see below.

### Adding or updating translations

Copy the keys you want to translate from `en.ts` and translate their values. Keep the
placeholders like `{{text}}` and the tags like `<issueLink>…</issueLink>` as they are.

There is a command to check that no keys are missing:

```bash
npm run i18n:check         # number of missing translations per language
npm run i18n:check -- de   # also lists the keys missing in `de`
```

When you add a new text to the interface, add its key to `en.ts` and, if you can, to the other
languages.
