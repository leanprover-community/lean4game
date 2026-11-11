import { atomWithQuery } from 'jotai-tanstack-query'

import type { ApiClientConfig, ApiLocalised } from '../api'
import { fetchJson } from '../utils/fetch'

/** The public part of the server config */
export const configAtom = atomWithQuery(() => ({
  queryKey: ['config'],
  queryFn: () => fetchJson<ApiClientConfig>('/api/config'),
  staleTime: Infinity,
}))

/** The text of `localised` in the language `lng`, falling back to English */
export function localise(localised: ApiLocalised, lng: string): string {
  if (typeof localised === 'string') return localised
  return localised[lng] ?? localised.en ?? Object.values(localised)[0] ?? ''
}
