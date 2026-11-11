import { atomFamily } from 'jotai-family'
import { atomWithQuery } from 'jotai-tanstack-query'

import type { ApiGameData } from '../api'
import { fetchJson, gameDataUrl, retryUnlessClientError } from '../utils/fetch'

/**
 * The `game.json` of the game `gameId`, e.g. `g/owner/repo`. In its own file, as
 * `location-atoms` needs it to resolve the world in the URL.
 */
export const gameInfoAtomFamily = atomFamily((gameId: string) =>
  atomWithQuery<ApiGameData>(() => ({
    queryKey: ['gameInfo', gameId],
    queryFn: () => fetchJson<ApiGameData>(gameDataUrl(gameId, 'game')),
    enabled: gameId.length > 0,
    retry: retryUnlessClientError,
  })),
)
