import * as React from 'react'
import ReactCountryFlag from 'react-country-flag'
import lean4gameConfig from '../config.json'

/** Displays either a flag or the language-code, depending on the settings.
 * The argument `iso` is an ISO-language code.
 */
export const Flag : React.FC<{ iso: string, showTitle?: boolean}> = ({iso, showTitle=false}) => {
  let lang = lean4gameConfig.languages[iso]
  if (lean4gameConfig.useFlags && lang) {
    return <ReactCountryFlag countryCode={lang.flag} title={showTitle ? lang.name : null} />
  }
  return <span>{iso}</span>
}
