import fs from 'node:fs/promises'
import path from 'node:path'

import type { ApiGameActivityStats, ApiGameImportStats } from './api.js'
import {
  addGameActivity,
  getGameActivity,
  getImportStats,
} from './database/db.js'
import { importedGames } from './import/imported.js'
import type { LeanInstance } from './lean/leanInstances.js'

/**
 * The import statistics of all imported games, featured or not, including games which
 * are not (fully) built.
 */
export async function listImportStats(): Promise<ApiGameImportStats[]> {
  const stats = getImportStats()
  const result: ApiGameImportStats[] = []
  for (const { owner, repo, gamePath } of await importedGames()) {
    const toolchain = await readToolchain(gamePath)
    const history = stats.get(`${owner}/${repo}`)
    result.push({
      owner,
      repo,
      toolchain,
      leanVersion: toolchain?.split(':')[1] ?? null,
      firstImportedAt: history?.firstImportedAt ?? null,
      lastImportedAt: history?.lastImportedAt ?? null,
      importCount: history?.importCount ?? 0,
      importsPerDay: history?.importsPerDay ?? {},
      fullyBuilt: history?.fullyBuilt ?? null,
    })
  }
  return result
}

async function readToolchain(gamePath: string): Promise<string | null> {
  return fs
    .readFile(path.join(gamePath, 'lean-toolchain'), 'utf-8')
    .then(content => content.trim())
    .catch(() => null)
}

/** A gap between two checks longer than this counts as a break */
const IDLE_MS = (Number(process.env.STATS_IDLE_MINUTES) || 20) * 60_000

/** A language tag like `de` or `pt-br`, anything else becomes `unknown` */
function normalizeLanguage(language: unknown): string {
  if (
    typeof language === 'string' &&
    language.length <= 16 &&
    /^[a-z]{2,3}(-[a-z0-9]{2,8})*$/i.test(language)
  ) {
    return language.toLowerCase()
  }
  return 'unknown'
}

/**
 * The primary language of the first entry of an `Accept-Language` list, e.g. `fr` for
 * `fr-CH,fr;q=0.9,en;q=0.8`. Regions and further languages are dropped on purpose, as they
 * are not needed for the statistics.
 */
function preferredLanguage(acceptedLanguages: string[]): string {
  const first = acceptedLanguages.find(language => language !== '*')
  if (!first) return 'unknown'
  const primary = first.split('-')[0]
  return /^[a-z]{2,3}$/i.test(primary) ? primary.toLowerCase() : 'unknown'
}

/**
 * Adds a check to the anonymous play statistics. Only aggregated counters are stored,
 * nothing which identifies the instance or the player.
 */
export function recordCheck(
  instance: LeanInstance,
  language: unknown,
  /** the browser's languages from `Accept-Language`, by preference */
  acceptedLanguages: string[],
) {
  const now = Date.now()
  const gap =
    instance.lastCheckAt === undefined ? undefined : now - instance.lastCheckAt
  instance.lastCheckAt = now
  try {
    addGameActivity({
      ...instance.game,
      language: normalizeLanguage(language),
      preferredLanguage: preferredLanguage(acceptedLanguages),
      sessions: gap === undefined ? 1 : 0,
      checks: 1,
      playSeconds: gap !== undefined && gap <= IDLE_MS ? gap / 1000 : 0,
    })
  } catch (error) {
    // statistics must never break a check
    console.error('Could not record the play statistics:', error)
  }
}

/** The anonymous play statistics, optionally restricted to the intervals in `[from, to)` */
export function listGameActivity(
  from?: string,
  to?: string,
): ApiGameActivityStats[] {
  return getGameActivity(from, to)
}
