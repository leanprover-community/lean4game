/**
 * @fileOverview Define API of the server-client communication
*/
import { createApi, fetchBaseQuery } from '@reduxjs/toolkit/query/react'
import { InventoryTab } from './inventory-atoms'


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
  title?: string,
  introduction: string,
  info?: string,
  worlds?: {nodes: {[id:string]: {id: string, title: string, introduction: string, image: string}}, edges: string[][]},
  worldSize?: {[key: string]: number},
  authors?: string[],
  conclusion?: string,
  tile?: GameTile,
  image?: string
  settings?: {
    unbundleHyps: boolean,
  } | undefined
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
  lemmas: InventoryTile[],
  definitions: InventoryTile[],
  descrText: null|string,
  descrFormat: null|string,
  lemmaTab: null|string,
  statementName: null|string,
  displayName: null|string,
  template: null|string,
  image: null|string
}

/** Used to display the inventory on the welcome page */
export interface InventoryOverview {
  tactics: InventoryTile[],
  lemmas: InventoryTile[],
  definitions: InventoryTile[],
  lemmaTab: null,
}

export interface Doc {
  name: string,
  displayName: string,
  content: string,
  statement: string,
  type: string, // TODO: can I remove these?
  category: string,
}
