import { mkdirSync } from 'node:fs'
import path from 'node:path'
import { DatabaseSync } from 'node:sqlite'

import { migrate } from './migration.js'
import {
  DbInsertGameActivity,
  DbGameActivityRow,
  DbGameImportPerDayRow,
  DbGameImportPerGameRow,
  DbImportStats,
  DbInsertGameImport,
} from './models.js'

/**
 * We use a SQLite database which is a single file, `leangame.db`. The motivation is its
 * simplicity as it is already shipped with node.
 *
 * At startup, an existing database is migrated using `migrate()`.
 * To clear the database, simply delete the file while the server is stopped.
 */

const DATABASE_PATH = path.resolve(
  import.meta.dirname,
  '..',
  '..',
  process.env.DATABASE_PATH ?? path.join('data', 'leangame.db'),
)

function openDatabase(): DatabaseSync {
  mkdirSync(path.dirname(DATABASE_PATH), { recursive: true })
  const db = new DatabaseSync(DATABASE_PATH)
  migrate(db)
  return db
}

const db = openDatabase()

/** Records a successful import */
export function addImport(record: DbInsertGameImport): void {
  db.prepare(
    `INSERT INTO game_imports (owner, repo, imported_at, artifact_id, toolchain, fully_built)
     VALUES (?, ?, ?, ?, ?, ?)`,
  ).run(
    record.owner.toLowerCase(),
    record.repo.toLowerCase(),
    new Date().toISOString(),
    record.artifactId,
    record.toolchain,
    record.fullyBuilt ? 1 : 0,
  )
}

/**
 * Import statistics, aggregated per game.
 *
 * Aggregates the import statistic over all games and days where something has been
 * imported.
 */
export function getImportStats(): Map<string, DbImportStats> {
  const games: DbGameImportPerGameRow[] = db
    .prepare(
      `SELECT owner, repo, MIN(imported_at) AS first, MAX(imported_at) AS last,
         COUNT(*) AS count,
         (SELECT fully_built FROM game_imports AS latest
          WHERE latest.owner = g.owner AND latest.repo = g.repo
          ORDER BY imported_at DESC LIMIT 1) AS fullyBuilt
       FROM game_imports AS g GROUP BY owner, repo`,
    )
    .all() as unknown as DbGameImportPerGameRow[]
  const days: DbGameImportPerDayRow[] = db
    .prepare(
      `SELECT owner, repo, substr(imported_at, 1, 10) AS day, COUNT(*) AS count
       FROM game_imports GROUP BY owner, repo, day ORDER BY day`,
    )
    .all() as unknown as DbGameImportPerDayRow[]

  const stats = new Map<string, DbImportStats>()
  for (const game of games) {
    stats.set(`${game.owner}/${game.repo}`, {
      firstImportedAt: game.first,
      lastImportedAt: game.last,
      importCount: game.count,
      importsPerDay: {},
      fullyBuilt: game.fullyBuilt === 1,
    })
  }
  for (const { owner, repo, day, count } of days) {
    stats.get(`${owner}/${repo}`)!.importsPerDay[day] = count
  }
  return stats
}

/** The start of the current 30-minute interval, e.g. `"2026-10-22T14:30Z"` */
function currentInterval(): string {
  const now = new Date()
  now.setUTCMinutes(now.getUTCMinutes() < 30 ? 0 : 30, 0, 0)
  return now.toISOString().slice(0, 16) + 'Z'
}

/** Adds to the play statistics of the current interval */
export function addGameActivity(activity: DbInsertGameActivity): void {
  db.prepare(
    `INSERT INTO game_activity
       (interval, owner, repo, language, preferred_language, sessions, checks, play_seconds)
     VALUES (?, ?, ?, ?, ?, ?, ?, ?)
     ON CONFLICT (interval, owner, repo, language, preferred_language) DO UPDATE SET
       sessions = sessions + excluded.sessions,
       checks = checks + excluded.checks,
       play_seconds = play_seconds + excluded.play_seconds`,
  ).run(
    currentInterval(),
    activity.owner.toLowerCase(),
    activity.repo.toLowerCase(),
    activity.language,
    activity.preferredLanguage,
    activity.sessions,
    activity.checks,
    Math.round(activity.playSeconds),
  )
}

/** The play statistics, optionally restricted to the intervals in `[from, to)` */
export function getGameActivity(
  from?: string,
  to?: string,
): DbGameActivityRow[] {
  return db
    .prepare(
      `SELECT interval, owner, repo, language, preferred_language AS preferredLanguage,
         sessions, checks, play_seconds AS playSeconds
       FROM game_activity
       WHERE (? IS NULL OR interval >= ?) AND (? IS NULL OR interval < ?)
       ORDER BY interval, owner, repo, language, preferred_language`,
    )
    .all(
      from ?? null,
      from ?? null,
      to ?? null,
      to ?? null,
    ) as unknown as DbGameActivityRow[]
}
