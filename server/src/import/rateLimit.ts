/*
Limits how often a game can be imported, as an import downloads the game from GitHub and
stops its running instances. The imports are only counted in memory, so restarting the
server resets the limits.
*/

const MINUTE = 60_000
const HOUR = 60 * MINUTE

const LIMITS = [
  { max: 1, windowMs: MINUTE, label: '1 per minute' },
  { max: 10, windowMs: HOUR, label: '10 per hour' },
]

export interface ImportRateLimitHit {
  /** the limit which was reached, e.g. `1 per minute` */
  label: string
  /** when the import is possible again */
  retryAfterSeconds: number
}

/** The times of the imports in the last hour by game, oldest first */
const importTimes = new Map<string, number[]>()

/**
 * Counts an import of the game `key`, unless this exceeds a limit. In that case the limit
 * with the longest wait is returned and nothing is counted.
 */
export function takeImportSlot(
  key: string,
  now = Date.now(),
): ImportRateLimitHit | undefined {
  const times = importTimes.get(key) ?? []
  let hit: ImportRateLimitHit | undefined
  for (const { max, windowMs, label } of LIMITS) {
    const inWindow = times.filter(time => now - time < windowMs)
    if (inWindow.length < max) continue
    // possible again once enough of these imports have left the window
    const freeAt = inWindow[inWindow.length - max] + windowMs
    const retryAfterSeconds = Math.ceil((freeAt - now) / 1000)
    if (!hit || retryAfterSeconds > hit.retryAfterSeconds) {
      hit = { label, retryAfterSeconds }
    }
  }
  if (hit) return hit

  importTimes.set(key, [...times.filter(time => now - time < HOUR), now])
  for (const [game, gameTimes] of importTimes) {
    if (now - gameTimes[gameTimes.length - 1] >= HOUR) importTimes.delete(game)
  }
  return undefined
}
