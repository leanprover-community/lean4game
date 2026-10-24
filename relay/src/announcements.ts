import fs from 'node:fs/promises'
import type { RequestHandler } from 'express'

type LocalizedText = Record<string, string>

export interface Announcement {
  id: string
  priority?: number
  startsAt?: string
  endsAt?: string
  title: LocalizedText
  message: LocalizedText
}

function isObject(value: unknown): value is Record<string, unknown> {
  return value !== null && typeof value === 'object' && !Array.isArray(value)
}

function isLocalizedText(value: unknown): value is LocalizedText {
  return isObject(value) && typeof value.en === 'string' && value.en.trim() !== '' &&
    Object.values(value).every(text => typeof text === 'string' && text.trim() !== '')
}

function isTimestamp(value: unknown): value is string {
  // Require an explicit timezone so the schedule is independent of the server's timezone.
  return typeof value === 'string' &&
    /^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}(?:\.\d+)?(?:Z|[+-]\d{2}:\d{2})$/.test(value) &&
    Number.isFinite(Date.parse(value))
}

export function activeAnnouncements(data: unknown, now = Date.now()): Announcement[] {
  if (!isObject(data) || !Array.isArray(data.announcements)) {
    throw new Error('Expected an object containing an announcements array')
  }

  const ids = new Set<string>()
  const entries = data.announcements.map((entry, index): Announcement => {
    if (!isObject(entry) || typeof entry.id !== 'string' || !entry.id.trim() ||
        ids.has(entry.id) || !isLocalizedText(entry.title) || !isLocalizedText(entry.message) ||
        (entry.priority !== undefined && (typeof entry.priority !== 'number' || !Number.isFinite(entry.priority))) ||
        (entry.startsAt !== undefined && !isTimestamp(entry.startsAt)) ||
        (entry.endsAt !== undefined && !isTimestamp(entry.endsAt)) ||
        (typeof entry.startsAt === 'string' && typeof entry.endsAt === 'string' &&
          Date.parse(entry.startsAt) >= Date.parse(entry.endsAt))) {
      throw new Error(`Invalid announcement at index ${index}: use a unique id, English title/message, and valid dates/priority`)
    }
    ids.add(entry.id)
    return {
      id: entry.id,
      title: entry.title,
      message: entry.message,
      priority: entry.priority as number | undefined,
      startsAt: entry.startsAt as string | undefined,
      endsAt: entry.endsAt as string | undefined,
    }
  })

  return entries
    .filter(entry => (!entry.startsAt || now >= Date.parse(entry.startsAt)) &&
      (!entry.endsAt || now < Date.parse(entry.endsAt)))
    .sort((a, b) => (b.priority ?? 0) - (a.priority ?? 0))
}

/** Read on every request so operators can change notices without restarting the relay. */
export function announcementsHandler(filePath: string): RequestHandler {
  return async (_req, res) => {
    res.setHeader('Cache-Control', 'no-store')
    try {
      const raw = await fs.readFile(filePath, 'utf8')
      res.json({ announcements: activeAnnouncements(JSON.parse(raw)) })
    } catch (error: any) {
      if (error?.code === 'ENOENT') {
        res.json({ announcements: [] })
        return
      }
      console.error('Failed to read announcements:', error)
      res.status(503).json({ error: 'Announcements unavailable' })
    }
  }
}
