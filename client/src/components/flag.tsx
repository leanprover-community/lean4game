import * as React from 'react'
import ReactCountryFlag from 'react-country-flag'
import lean4gameConfig from '../config.json'
import { preferencesAtom } from '../store/preferences-atoms'
import { useAtom } from 'jotai'

/** Displays either a flag or the language-code, depending on the settings.
 * The argument `iso` is an ISO-language code.
 */
export function Flag({iso, showTitle=false} : { iso: string, showTitle?: boolean}) {
  const [preferences] = useAtom(preferencesAtom)
  let lang = lean4gameConfig.languages.find(it => it.iso == iso)
  if (preferences.useFlags && lang) {
    return <ReactCountryFlag countryCode={lang.flag} title={showTitle ? lang.name : undefined} />
  }
  return <span>{iso}</span>
}
