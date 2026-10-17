import assert from 'node:assert/strict'
import { mkdtemp, rm, writeFile } from 'node:fs/promises'
import { tmpdir } from 'node:os'
import path from 'node:path'
import { once } from 'node:events'
import { test } from 'node:test'
import express from 'express'
import { activeAnnouncements, announcementsHandler } from '../dist/src/announcements.js'

const entry = (id, extra = {}) => ({
  id,
  title: { en: 'Title' },
  message: { en: 'Message' },
  ...extra,
})

test('filters by inclusive start and exclusive end, with timezone offsets', () => {
  const now = Date.parse('2026-10-12T12:00:00Z')
  const result = activeAnnouncements({ announcements: [
    entry('permanent'),
    entry('starting-now', { startsAt: '2026-10-12T14:00:00+02:00' }),
    entry('ending-now', { endsAt: '2026-10-12T14:00:00+02:00' }),
    entry('future', { startsAt: '2026-10-12T12:00:01Z' }),
    entry('expired', { endsAt: '2026-10-12T11:59:59Z' }),
  ] }, now)
  assert.deepEqual(result.map(item => item.id), ['permanent', 'starting-now'])
})

test('orders by descending priority and preserves file order on ties', () => {
  const result = activeAnnouncements({ announcements: [
    entry('default'), entry('first-high', { priority: 100 }),
    entry('low', { priority: -1 }), entry('second-high', { priority: 100 }),
  ] })
  assert.deepEqual(result.map(item => item.id), ['first-high', 'second-high', 'default', 'low'])
  assert.deepEqual(activeAnnouncements({ announcements: [] }), [])
})

test('rejects invalid content, duplicate ids, and ambiguous schedules', () => {
  for (const data of [
    {}, { announcements: null },
    { announcements: [entry('a'), entry('a')] },
    { announcements: [entry('a', { title: { de: 'Titel' } })] },
    { announcements: [entry('a', { message: { en: '' } })] },
    { announcements: [entry('a', { priority: '100' })] },
    { announcements: [entry('a', { startsAt: '2026-10-12T14:00:00' })] },
    { announcements: [entry('a', { endsAt: 'not-a-date' })] },
    { announcements: [entry('a', {
      startsAt: '2026-10-12T12:00:00Z', endsAt: '2026-10-12T12:00:00Z',
    })] },
  ]) assert.throws(() => activeAnnouncements(data))
})

test('endpoint rereads edits, disables caching, handles missing and malformed files', async t => {
  const directory = await mkdtemp(path.join(tmpdir(), 'lean4game-announcements-'))
  t.after(() => rm(directory, { recursive: true, force: true }))
  const file = path.join(directory, 'announcements.json')
  const app = express().get('/data/announcements', announcementsHandler(file))
  const server = app.listen(0, '127.0.0.1')
  t.after(() => new Promise((resolve, reject) => {
    server.closeAllConnections()
    server.close(error => error ? reject(error) : resolve())
  }))
  await once(server, 'listening')
  const url = `http://127.0.0.1:${server.address().port}/data/announcements`

  let response = await fetch(url)
  assert.equal(response.status, 200)
  assert.equal(response.headers.get('cache-control'), 'no-store')
  assert.deepEqual(await response.json(), { announcements: [] })

  await writeFile(file, JSON.stringify({ announcements: [entry('first')] }))
  assert.equal((await (await fetch(url)).json()).announcements[0].id, 'first')
  await writeFile(file, JSON.stringify({ announcements: [entry('replacement')] }))
  assert.equal((await (await fetch(url)).json()).announcements[0].id, 'replacement')

  await writeFile(file, '{ invalid JSON')
  response = await fetch(url)
  assert.equal(response.status, 503)
  assert.equal(response.headers.get('cache-control'), 'no-store')
  assert.deepEqual(await response.json(), { error: 'Announcements unavailable' })

  await writeFile(file, JSON.stringify({ announcements: [entry('a'), entry('a')] }))
  assert.equal((await fetch(url)).status, 503)
  await writeFile(file, JSON.stringify({ announcements: [] }))
  assert.deepEqual(await (await fetch(url)).json(), { announcements: [] })
})
