import i18n from "i18next";
import Backend from "i18next-http-backend"
import { initReactI18next } from "react-i18next";
import type { GameSettings } from "./store/api";

i18n
.use(initReactI18next)
.use(Backend)
.init({
    ns: ['translation'],
    backend: {
      // > see https://github.com/i18next/i18next-http-backend
      loadPath: function(lngs: string[], namespaces: string[]) {
        const lng = lngs[0];
        const ns = namespaces[0]

        if (ns.startsWith("g/")) {
          return `/i18n/${ns}/${lng}`;
        } else {
          return `/locales/${lng}/${ns}.json`;
        }
      }
    },
    // > language to use, more information here:
    // > https://www.i18next.com/overview/configuration-options#languages-namespaces-resources
    lng: "en",
    // Fallback to English if other translations are missing
    fallbackLng: "en",
    // > you can use the i18n.changeLanguage function to change the language manually:
    // > https://www.i18next.com/overview/api#changelanguage
    // > if you're using a language detector, do not define the lng option
    returnEmptyString: false,
    nsSeparator: false, // to allow `:` in the key
    interpolation: {
      // > react already safes from xss
      escapeValue: false
    }
  });

const gameI18nInstances = new Map<string, typeof i18n>()

/**
 * Return an i18next instance for game strings.
 *
 * The clone shares loaded resources with the main instance, but keeps game
 * fallback and missing-translation policy separate from the interface and
 * other games.
 */
export function getGameI18n(settings?: GameSettings): typeof i18n {
  const fallbackLanguage = settings?.fallbackLanguage ?? "en"
  const allowEmptyTranslations = settings?.allowEmptyTranslations ?? false
  const hideMissingTranslations = settings?.hideMissingTranslations ?? false

  if (fallbackLanguage === "en" && !allowEmptyTranslations && !hideMissingTranslations) {
    return i18n
  }

  const key = JSON.stringify({ fallbackLanguage, allowEmptyTranslations, hideMissingTranslations })
  let gameI18n = gameI18nInstances.get(key)
  if (!gameI18n) {
    gameI18n = i18n.cloneInstance({
      fallbackLng: fallbackLanguage,
      returnEmptyString: allowEmptyTranslations || hideMissingTranslations,
    })
    gameI18nInstances.set(key, gameI18n)
  }
  return gameI18n
}

export default i18n;
