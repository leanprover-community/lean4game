import { atom } from 'jotai'
import { atomWithQuery } from 'jotai-tanstack-query'

import type { ApiImportStatus } from '../api'
import { fetchJson, postJson, retryUnlessClientError } from '../utils/fetch'

function importUrl(owner: string, repo: string) {
  return `/api/import/${encodeURIComponent(owner)}/${encodeURIComponent(repo)}`
}

/** The import shown on the import page */
export const currentImportAtom = atom<{
  owner: string
  repo: string
  startedAt: string
} | null>(null)

/** Asks the server to import the game, which continues a running import of it */
export const startImportAtom = atom(
  null,
  async (_get, set, owner: string, repo: string) => {
    const { startedAt } = await postJson<ApiImportStatus>(
      `${importUrl(owner, repo)}/trigger`,
    )
    set(currentImportAtom, { owner, repo, startedAt })
  },
)

/** The status of the current import, updated every second while it is running */
export const importStatusAtom = atomWithQuery<ApiImportStatus>(get => {
  const current = get(currentImportAtom)
  return {
    queryKey: ['import', current],
    queryFn: () =>
      fetchJson<ApiImportStatus>(importUrl(current!.owner, current!.repo)),
    enabled: current !== null,
    refetchInterval: query =>
      query.state.data?.state === 'running' && !query.state.error
        ? 1000
        : false,
    retry: retryUnlessClientError,
  }
})
