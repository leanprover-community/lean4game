import i18n from 'i18next'
import Backend from 'i18next-http-backend'
import { initReactI18next } from 'react-i18next'

import config from './config.json'
import { de } from './translations/de'
import { en } from './translations/en'
import { es } from './translations/es'
import { fr } from './translations/fr'
import { it } from './translations/it'
import { ko } from './translations/ko'
import { ptBR } from './translations/pt-BR'
import { ru } from './translations/ru'
import { uk } from './translations/uk'
import { zh } from './translations/zh'

/** The language of new visitors, can be set at build time */
export const DEFAULT_LANGUAGE: string =
  import.meta.env.VITE_CLIENT_DEFAULT_LANGUAGE || 'en'

/** The URL parameter for the language, e.g. `?lang=de` */
export const LANGUAGE_PARAM = 'lang'

/** The language given in the URL, if it is one of the languages of the interface */
function urlLanguage(): string | undefined {
  const lng = new URLSearchParams(window.location.search).get(LANGUAGE_PARAM)
  return config.languages.some(l => l.iso === lng)
    ? (lng ?? undefined)
    : undefined
}

/** Same key as `i18next-browser-languagedetector` uses */
const LANGUAGE_KEY = 'i18nextLng'

/** The language saved in the browser, if any */
function savedLanguage(): string | undefined {
  try {
    return localStorage.getItem(LANGUAGE_KEY) ?? undefined
  } catch {
    // storage can be blocked by the browser
    return undefined
  }
}

/** Switches to the language `lng` and remembers it in the browser */
export function setLanguage(lng: string) {
  void i18n.changeLanguage(lng)
  try {
    localStorage.setItem(LANGUAGE_KEY, lng)
  } catch {
    // the language is just not remembered
  }
}

void i18n
  .use(initReactI18next)
  .use(Backend)
  .init({
    ns: ['translation'],
    backend: {
      // > see https://github.com/i18next/i18next-http-backend
      loadPath: function (lngs: string[], namespaces: string[]) {
        const lng = lngs[0]
        const ns = namespaces[0]

        // the translations of a game, see `useGameTranslation`
        if (ns.startsWith('g/')) {
          return `/api/i18n/${ns.slice(2)}/${lng}`
        } else {
          return `/locales/${lng}/${ns}.json`
        }
      },
    },
    // the interface's translations are bundled, but the games' ones are loaded
    partialBundledLanguages: true,
    // > language to use, more information here:
    // > https://www.i18next.com/overview/configuration-options#languages-namespaces-resources
    // a link with `?lang=` wins over the saved language, but is not saved itself
    lng: urlLanguage() ?? savedLanguage() ?? DEFAULT_LANGUAGE,
    // Fallback to English if other translations are missing
    fallbackLng: 'en',
    // > you can use the i18n.changeLanguage function to change the language manually:
    // > https://www.i18next.com/overview/api#changelanguage
    // > if you're using a language detector, do not define the lng option
    returnEmptyString: false,
    nsSeparator: false, // to allow `:` in the key
    interpolation: {
      // > react already safes from xss
      escapeValue: false,
    },
    resources: {
      de: { translation: de },
      en: { translation: en },
      es: { translation: es },
      fr: { translation: fr },
      it: { translation: it },
      ko: { translation: ko },
      'pt-BR': { translation: ptBR },
      ru: { translation: ru },
      uk: { translation: uk },
      zh: { translation: zh },
    },
  })

let emptyStringI18n: typeof i18n | undefined

/**
 * Return an i18next instance for game strings.
 *
 * The clone shares loaded resources with the main instance, but treats an
 * explicit empty string as a valid translation. Keeping this option on a
 * separate instance prevents intentionally empty game strings from changing
 * fallback behaviour for the interface or for games which have not opted in.
 */
export function getGameI18n(allowEmptyTranslations: boolean): typeof i18n {
  if (!allowEmptyTranslations) return i18n
  emptyStringI18n ??= i18n.cloneInstance({ returnEmptyString: true })
  return emptyStringI18n
}

export default i18n
