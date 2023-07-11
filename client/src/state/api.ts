/**
 * @fileOverview Define API of the server-client communication
*/
import { createApi, fetchBaseQuery } from '@reduxjs/toolkit/query/react'
import { Connection } from '../connection'

interface GameInfo {
  title: null|string,
  introduction: null|string,
  worlds: null|{nodes: {[id:string]: {id: string, title: string, introduction: string}}, edges: string[][]},
  worldSize: null|{[key: string]: number},
  authors: null|string[],
  conclusion: null|string,
}

export interface InventoryTile {
  name: string,
  displayName: string,
  category: string,
  disabled: boolean,
  locked: boolean,
  new: boolean
}

export interface LevelInfo {
  title: null|string,
  introduction: null|string,
  conclusion: null|string,
  index: number,
  tactics: InventoryTile[],
  lemmas: InventoryTile[],
  definitions: InventoryTile[],
  descrText: null|string,
  descrFormat: null|string,
  lemmaTab: null|string,
  statementName: null|string
}

interface Doc {
  name: string,
  displayName: string,
  content: string,
  statement: string,
  type: string, // TODO: can I remove these?
  category: string,
}


const customBaseQuery = async (
  args : {game: string, method: string, params?: any},
  { signal, dispatch, getState, extra },
  extraOptions
) => {
  try {
    const connection : Connection = extra.connection
    let leanClient = await connection.startLeanClient(args.game)
    console.log(`Sending request ${args.method}`)
    let res = await leanClient.sendRequest(args.method, args.params)
    console.log('Received response') //, res)
    return {'data': res}
   } catch (e) {
    return {'error': e}
   }
}

// Define a service using a base URL and expected endpoints
export const apiSlice = createApi({
  reducerPath: 'gameApi',
  baseQuery: customBaseQuery,
  endpoints: (builder) => ({
    getGameInfo: builder.query<GameInfo, {game: string}>({
      query: ({game}) => {return {game, method: 'info', params: {}}},
    }),
    loadLevel: builder.query<LevelInfo, {game: string, world: string, level: number}>({
      query: ({game, world, level}) => {return {game, method: "loadLevel", params: {world, level}}},
    }),
    loadDoc: builder.query<Doc, {game: string, name: string, type: "lemma"|"tactic"}>({
      query: ({game, name, type}) => {return {game, method: "loadDoc", params: {name, type}}},
    }),
  }),
})

// Export hooks for usage in functional components, which are
// auto-generated based on the defined endpoints
export const { useGetGameInfoQuery, useLoadLevelQuery, useLoadDocQuery } = apiSlice
