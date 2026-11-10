import path from 'node:path'

import express from 'express'

import type { ApiClientConfig, ApiProofCheckInput } from './api.js'
import { serveClient } from './client.js'
import { readConfig } from './config.js'
import {
  gameDataFilePath,
  i18nFilePath,
  isTestGame,
  listGames,
  requireGame,
} from './gameData.js'
import {
  getImportStatus,
  isValidRepoName,
  startImport,
} from './import/gameImport.js'
import {
  countActiveInstances,
  getAllInstances,
  getInstance,
  startInstance,
  stopInstance,
  touchInstance,
} from './lean/leanInstances.js'
import {
  CheckSupersededError,
  CheckTimeoutError,
} from './lean/openDocuments.js'
import { checkProof } from './lean/proofCheck.js'
import { getServerLoad } from './serverLoad.js'
import { listGameActivity, listImportStats, recordCheck } from './stats.js'
import { isDevMode } from './utils/devMode.js'
import { sendJsonFile } from './utils/response.js'

const PORT = Number(process.env.PORT) || 8000
/** e.g. `127.0.0.1` to only accept connections from a reverse proxy on the same machine */
const HOST = process.env.HOST
const app = express()
app.use(express.json())

app.post('/api/lean/start/:owner/:game', (req, res) => {
  const game = req.params.game
  const owner = req.params.owner
  const gamePath = requireGame(owner, game, res)
  if (!gamePath) return
  try {
    const instance = startInstance(
      gamePath,
      { owner: owner.toLowerCase(), repo: game.toLowerCase() },
      isTestGame(owner, game),
    )
    res.status(201).json({
      id: instance.id,
      status: instance.status,
      startedAt: instance.startedAt,
    })
  } catch (error) {
    // TODO: do not expose error message, write to logs instead
    res.status(500).json({
      error: `Failed to start Lean server: ${(error as Error).message}`,
    })
  }
})

// // TODO: this is for debugging only. We should remove it eventually
// app.get('/api/lean/instances', (req, res) => {
//   const instances = getAllInstances()
//   res.json(
//     instances.map(instance => ({
//       id: instance.id,
//       status: instance.status,
//       startedAt: instance.startedAt,
//       exitCode: instance.exitCode,
//     })),
//   )
// })

// must be registered before '/api/lean/instances/:id'
app.get('/api/lean/instances/count', (_req, res) => {
  res.json(countActiveInstances())
})

app.get('/api/lean/instances/:id', (req, res) => {
  const instance = getInstance(req.params.id)
  if (!instance) {
    res.status(404).json({ error: 'Instance not found' })
    return
  }
  res.json({
    id: instance.id,
    status: instance.status,
    startedAt: instance.startedAt,
    exitCode: instance.exitCode,
  })
})

// TODO: we might not need this if we have the identical `/stop` below.
app.delete('/api/lean/instances/:id', (req, res) => {
  const found = stopInstance(req.params.id)
  if (!found) {
    res.status(404).json({ error: 'Instance not found' })
    return
  }
  const instance = getInstance(req.params.id)!
  res.json({ id: instance.id, status: instance.status })
})

// same as `DELETE` on `/api/lean/instances/:id`, for convenience
app.post('/api/lean/instances/:id/stop', (req, res) => {
  const found = stopInstance(req.params.id)
  if (!found) {
    res.status(404).json({ error: 'Instance not found' })
    return
  }
  const instance = getInstance(req.params.id)!
  res.json({ id: instance.id, status: instance.status })
})

app.post('/api/lean/instances/:id/keepalive', (req, res) => {
  if (!touchInstance(req.params.id)) {
    res.status(404).json({ error: 'Instance not found' })
    return
  }
  res.status(204).end()
})

app.post('/api/lean/instances/:id/check', async (req, res) => {
  const input: ApiProofCheckInput = req.body
  // TODO: validate input
  const instance = getInstance(req.params.id)
  if (!instance) {
    res.status(404).json({ error: 'Instance not found' })
    return
  }
  recordCheck(instance, input.language, req.acceptsLanguages())
  touchInstance(instance.id)
  try {
    const result = await checkProof({ ...input, instance })
    res.json(result)
  } catch (error) {
    if (error instanceof CheckSupersededError) {
      res.status(409).json({ error: error.message })
      return
    }
    if (error instanceof CheckTimeoutError) {
      res.status(504).json({ error: error.message })
      return
    }
    // TODO: do not expose error message, write to logs instead
    res
      .status(500)
      .json({ error: `Failed to check proof: ${(error as Error).message}` })
  } finally {
    // a long check must not count as idle time
    touchInstance(instance.id)
  }
})

app.get('/api/games', async (_req, res) => {
  res.json(await listGames())
})

app.get('/api/config', async (_req, res) => {
  const { announcements, contact, impressum, privacy } = await readConfig()
  res.json({
    announcements,
    contact,
    impressum,
    privacy,
  } satisfies ApiClientConfig)
})

app.get('/api/load', (_req, res) => {
  res.json(getServerLoad())
})

app.post('/api/import/:owner/:repo/trigger', (req, res) => {
  const { owner, repo } = req.params
  if (!isValidRepoName(owner, repo)) {
    res.status(400).json({ error: 'Invalid repository name' })
    return
  }
  const result = startImport(owner, repo)
  if ('retryAfterSeconds' in result) {
    res
      .status(429)
      .set('Retry-After', String(result.retryAfterSeconds))
      .json({ error: `Rate limit of ${result.label} reached` })
    return
  }
  res.status(202).json(result)
})

app.get('/api/import/:owner/:repo', (req, res) => {
  const status = getImportStatus(req.params.owner, req.params.repo)
  if (!status) {
    res.status(404).json({ error: 'No import found' })
    return
  }
  res.json(status)
})

app.get('/api/data/:owner/:game/game', (req, res) => {
  const gamePath = requireGame(req.params.owner, req.params.game, res)
  if (!gamePath) return
  void sendJsonFile(res, gameDataFilePath(gamePath, 'game.json'))
})

app.get('/api/data/:owner/:game/inventory', (req, res) => {
  const gamePath = requireGame(req.params.owner, req.params.game, res)
  if (!gamePath) return
  void sendJsonFile(
    res,
    path.join(gamePath, '.lake', 'gamedata', 'inventory.json'),
  )
})

app.get('/api/data/:owner/:game/level/:world/:level', (req, res) => {
  const gamePath = requireGame(req.params.owner, req.params.game, res)
  if (!gamePath) return
  void sendJsonFile(
    res,
    gameDataFilePath(
      gamePath,
      `level__${req.params.world}__${req.params.level}.json`,
    ),
  )
})

app.get('/api/data/:owner/:game/doc/:kind/:name', (req, res) => {
  const gamePath = requireGame(req.params.owner, req.params.game, res)
  if (!gamePath) return
  void sendJsonFile(
    res,
    gameDataFilePath(
      gamePath,
      // the files are lowercase, e.g. `doc__tactic__rw.json`. Case-insensitive file
      // systems like macOS's would hide a wrong case, so normalize it here.
      `doc__${req.params.kind.toLowerCase()}__${req.params.name}.json`,
    ),
  )
})

app.get('/api/data/:owner/:game/images/*file', (req, res) => {
  const gamePath = requireGame(req.params.owner, req.params.game, res)
  if (!gamePath) return
  // with `root`, `sendFile` refuses paths outside the `images/` folder and only refuses
  // dotfiles below it, not the `.lake` folder in `root` itself
  const root = path.join(gamePath, '.lake', 'gamedata', 'images')
  res.sendFile(req.params.file.join('/'), { root }, err => {
    if (err && !res.headersSent) res.status(404).json({ error: 'Not found' })
  })
})

app.get('/api/i18n/:owner/:game/:lang', (req, res) => {
  const gamePath = requireGame(req.params.owner, req.params.game, res)
  if (!gamePath) return
  void sendJsonFile(res, i18nFilePath(gamePath, req.params.lang))
})

// // TODO: these endpoints need some sort of authentification
// app.get('/stats/games', (req, res) => {
//   const { from, to } = req.query
//   res.json(
//     listGameActivity(
//       typeof from === 'string' ? from : undefined,
//       typeof to === 'string' ? to : undefined,
//     ),
//   )
// })
//
// app.get('/stats/imports', async (_req, res) => {
//   res.json(await listImportStats())
// })

// in development, Vite serves the client
if (!isDevMode()) serveClient(app)

const onListening = () =>
  console.log(`Server listening on ${HOST ?? ''}:${PORT}`)
// without a host, Node listens on all addresses (IPv4 and IPv6)
if (HOST) app.listen(PORT, HOST, onListening)
else app.listen(PORT, onListening)
