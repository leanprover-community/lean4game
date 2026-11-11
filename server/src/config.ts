import fs from 'node:fs/promises'
import path from 'node:path'

import type { ApiClientConfig } from './api.js'

/*
The server's configuration file, by default `server/config.json`. It is read on every use,
so changes apply without a restart.
*/

const CONFIG_PATH = path.resolve(
  import.meta.dirname,
  '..',
  process.env.CONFIG_PATH ?? 'config.json',
)

export interface ServerConfig extends ApiClientConfig {
  /** The games listed first on the landing page, in this order */
  featuredGames: { owner: string; repo: string }[]
  /**
   * Whether `/api/games` also lists the imported games which are not featured.
   * `/stats/imports` always lists all imported games.
   */
  listImportedGames: boolean
}

const DEFAULT_CONFIG: ServerConfig = {
  announcements: [],
  featuredGames: [],
  listImportedGames: false,
}

/** The configuration, with defaults for a missing file or missing fields */
export async function readConfig(): Promise<ServerConfig> {
  let content: string
  try {
    content = await fs.readFile(CONFIG_PATH, 'utf-8')
  } catch (error) {
    if ((error as NodeJS.ErrnoException).code === 'ENOENT')
      return DEFAULT_CONFIG
    throw error
  }
  return {
    ...DEFAULT_CONFIG,
    ...(JSON.parse(content) as Partial<ServerConfig>),
  }
}
