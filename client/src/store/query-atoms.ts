import { atomWithQuery } from 'jotai-tanstack-query'
import { gameIdAtom, levelIdAtom, worldIdAtom } from './location-atoms'
import { Doc, GameInfo, InventoryOverview, LevelInfo } from '../state/api'
import { atomFamily } from 'jotai/utils'
import { atom } from 'jotai'
import { InventoryTab } from './inventory-atoms'

/** The info about all games */
export const gameInfoAtomFamily = atomFamily((gameId: string) => atomWithQuery<GameInfo>(() => {
  return {
    queryKey: ['gameInfo', gameId],
    queryFn: async () => {
      const res = await fetch(`${window.location.origin}/data/${gameId}/game.json`)
      return res.json()
    },
    enabled: gameId.length > 0,
  }
}))

/** The info about the current game */
export const gameInfoAtom = atom((get) => {
  const gameId = get(gameIdAtom)
  return get(gameInfoAtomFamily(gameId ?? ""))
})

/** Info about the current level */
export const levelInfoAtom = atomWithQuery<LevelInfo>((get) => {
  const gameId = get(gameIdAtom)
  const worldId = get(worldIdAtom)
  const levelId = get(levelIdAtom)
  return {
    queryKey: ['levelInfo', gameId, worldId, levelId],
    queryFn: async () => {
      const res = await fetch(`${window.location.origin}/data/${gameId}/level__${worldId}__${levelId}.json`)
      return res.json()
    },
  }
})
