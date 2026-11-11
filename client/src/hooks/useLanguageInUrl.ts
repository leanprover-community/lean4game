import { useAtom } from 'jotai'
import { useEffect } from 'react'
import { useTranslation } from 'react-i18next'

import { DEFAULT_LANGUAGE, LANGUAGE_PARAM } from '../i18n'
import { locationAtom } from '../state/location-atoms'

/**
 * Keeps `?lang=` in the URL in sync with the current language, so that links include
 * it. It is omitted for the default language. Replaces the history entry instead of
 * adding one.
 */
export function useLanguageInUrl() {
  const { i18n } = useTranslation()
  const [location, setLocation] = useAtom(locationAtom)
  const urlLanguage = location.searchParams?.get(LANGUAGE_PARAM) ?? undefined
  const language =
    i18n.language === DEFAULT_LANGUAGE ? undefined : i18n.language

  useEffect(() => {
    if (urlLanguage === language) return
    setLocation(
      prev => {
        const searchParams = new URLSearchParams(prev.searchParams)
        if (language) searchParams.set(LANGUAGE_PARAM, language)
        else searchParams.delete(LANGUAGE_PARAM)
        return { ...prev, searchParams }
      },
      { replace: true },
    )
  }, [urlLanguage, language, setLocation])
}
