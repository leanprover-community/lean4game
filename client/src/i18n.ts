import i18n from "i18next";
import Backend from "i18next-http-backend"
import { initReactI18next } from "react-i18next";

i18n
.use(initReactI18next)
.use(Backend)
.init({
    ns: ['translation'],
    backend: {
      // > see https://github.com/i18next/i18next-http-backend
      loadPath: function(lngs, namespaces: Array<string>) {
        const lng = namespaces[0] === "g/hhu-adam/robo" ? "de" : lngs[0];

        if (namespaces[0].startsWith("g/")) {
          return `/i18n/${namespaces[0]}/${lng}/Game.json`;
        } else {
          return `/locales/${lng}/${namespaces[0]}.json`;
        }
      }
    },
    // > language to use, more information here:
    // > https://www.i18next.com/overview/configuration-options#languages-namespaces-resources
    lng: "en",
    // we use natural language keys, so we don't need a fallback language.
    fallbackLng: false,
    // > you can use the i18n.changeLanguage function to change the language manually:
    // > https://www.i18next.com/overview/api#changelanguage
    // > if you're using a language detector, do not define the lng option
    returnEmptyString: false,
    interpolation: {
      // > react already safes from xss
      escapeValue: false
    }
  });

  export default i18n;
