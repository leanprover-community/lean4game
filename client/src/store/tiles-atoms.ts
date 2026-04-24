import { atomWithQuery } from "jotai-tanstack-query"
import { GameTileWithName } from "./api"
import { atom } from "jotai"


const gameTilesQueryAtom = atomWithQuery<GameTileWithName[]>((get) => {
  return {
    queryKey: ['gameTiles'],
    queryFn: async () => {
      const res = await fetch(`${window.location.origin}/api/games`)
      return res.json()
    },
  }
})

/** Tiles of all available games */
export const gameTilesAtom = atom(get => get(gameTilesQueryAtom).data ?? [])
