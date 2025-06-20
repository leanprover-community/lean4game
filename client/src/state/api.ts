/**
 * @fileOverview Define API of the server-client communication
*/
import { createApi, fetchBaseQuery } from '@reduxjs/toolkit/query/react'


export interface GameTile {
  title: string
  short: string
  long: string
  languages: Array<string>
  prerequisites: Array<string>
  worlds: number
  levels: number
  image: string
}

export interface GameInfo {
  title: null|string,
  introduction: null|string,
  info: null|string,
  worlds: null|{nodes: {[id:string]: {id: string, title: string, introduction: string, image: string}}, edges: string[][]},
  worldSize: null|{[key: string]: number},
  authors: null|string[],
  conclusion: null|string,
  tile: null|GameTile,
  image: null|string
}

export interface InventoryTile {
  name: string,
  displayName: string,
  category: string,
  disabled: boolean,
  locked: boolean,
  new: boolean,
  hidden: boolean
  altTitle: string,
  world : string|null,
  level : number|null,
  proven : boolean
}

export interface LevelInfo {
  title: null|string,
  introduction: null|string,
  conclusion: null|string,
  index: number,
  tactics: InventoryTile[],
  theorems: InventoryTile[],
  definitions: InventoryTile[],
  descrText: null|string,
  descrFormat: null|string,
  theoremTab: null|string,
  statementName: null|string,
  displayName: null|string,
  template: null|string,
  image: null|string
}

/** Used to display the inventory on the welcome page */
export interface InventoryOverview {
  tactics: InventoryTile[],
  theorems: InventoryTile[],
  definitions: InventoryTile[],
  theoremTab: null,
}

interface Doc {
  name: string,
  displayName: string,
  content: string,
  statement: string,
  type: string, // TODO: can I remove these?
  category: string,
}

// Define a service using a base URL and expected endpoints
export const apiSlice = createApi({
  reducerPath: 'gameApi',
  baseQuery: fetchBaseQuery({ baseUrl: window.location.origin + "/data" }),
  endpoints: (builder) => ({
    getGameInfo: builder.query<GameInfo, {game: string}>({
      query: ({game}) => `${game}/game.json`,
    }),
    loadLevel: builder.query<LevelInfo, {game: string, world: string, level: number}>({
      query: ({game, world, level}) => {
        if (world && level > 0) {
          return `${game}/level__${world}__${level}.json`
        } else {
          return `${game}/inventory.json`
        }
      },
    }),
    loadInventoryOverview: builder.query<InventoryOverview, {game: string}>({
      query: ({game}) => `${game}/inventory.json`,
    }),
    loadDoc: builder.query<Doc, {game: string, name: string }>({
      query: ({game, name}) => `${game}/doc__${name}.json`,
    }),
  }),
})

// Export hooks for usage in functional components, which are
// auto-generated based on the defined endpoints
export const { useGetGameInfoQuery, useLoadLevelQuery, useLoadDocQuery, useLoadInventoryOverviewQuery } = apiSlice
