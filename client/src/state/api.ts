import { createApi, fetchBaseQuery } from '@reduxjs/toolkit/query/react'
import { Connection } from '../connection'

interface GameInfo {
  title: null|string,
  introduction: null|string,
  worlds: null|{nodes: {[id:string]: {id: string, title: string}}, edges: string[][]},
  worldSize: null|{[key: string]: number},
  authors: null|string[],
  conclusion: null|string,
}

interface LevelInfo {
  title: null|string,
  introduction: null|string,
  index: number,
  tactics: {name: string, disabled: boolean, locked: boolean}[],
  lemmas: any[],
  descrText: null|string,
  descrFormat: null|string,
}

const customBaseQuery = async (
  args : {method: string, params?: any},
  { signal, dispatch, getState, extra },
  extraOptions
) => {
  try {
    const connection : Connection = extra.connection
    let leanClient = await connection.startLeanClient()
    console.log(`Sending request ${args.method}`)
    let res = await leanClient.sendRequest(args.method, args.params)
    console.log('Received response', res)
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
    getGameInfo: builder.query<GameInfo, void>({
      query: () => {return {method: 'info', params: {}}},
    }),
    loadLevel: builder.query<LevelInfo, {world: string, level: number}>({
      query: ({world, level}) => {return {method: "loadLevel", params: {world, level}}},
    }),
  }),
})

// Export hooks for usage in functional components, which are
// auto-generated based on the defined endpoints
export const { useGetGameInfoQuery, useLoadLevelQuery } = apiSlice
