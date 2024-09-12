import { WebSocketServer } from 'ws'
import express from 'express'
import * as cp from 'child_process'
import * as url from 'url'
import * as rpc from 'vscode-ws-jsonrpc'
import * as path from 'path'
import * as jsonrpcserver from 'vscode-ws-jsonrpc/server'
// import nocache from 'nocache'
import anonymize from 'ip-anonymize'
import os from 'os'
import fs from 'fs'
import http from 'http'
import https from 'https'

import { importTrigger, importStatus } from './import.mjs'

/**
 * Add a game here if the server should keep a queue of pre-loaded games ready at all times.
 *
 * IMPORTANT! Tags here need to be lower case!
*/
const queueLength = {
  "g/hhu-adam/robo": 2,
  "g/hhu-adam/nng4": 5,
  "g/djvelleman/stg4": 0,
  "g/trequetrum/lean4game-logic": 0,
}

let socketCounter = 0

function logStats() {
  console.log(`[${new Date()}] Number of open sockets - ${socketCounter}`)
  console.log(`[${new Date()}] Free RAM - ${Math.round(os.freemem() / 1024 / 1024)} / ${Math.round(os.totalmem() / 1024 / 1024)} MB`)
}

const __filename = url.fileURLToPath(import.meta.url)
const __dirname = url.fileURLToPath(new URL('.', import.meta.url))


const environment = process.env.NODE_ENV
const isDevelopment = environment === 'development'

const crtFile = process.env.SSL_CRT_FILE
const keyFile = process.env.SSL_KEY_FILE

const app = express()

var router = express.Router()

// Paths for game import logic
router.get('/import/status/:owner/:repo', importStatus)
router.get('/import/trigger/:owner/:repo', importTrigger)

app.use(express.static(path.join(__dirname, '..', 'client', 'dist'))) // TODO: add a dist folder from inside the game
app.use('/i18n/g/:owner/:repo/:lang/*', (req, res, next) => {
    const owner = req.params.owner
    const repo = req.params.repo
    const lang = req.params.lang
    const filename = req.params[0]
    req.url = filename
    express.static(path.join(getGameDir(owner,repo),".i18n",lang))(req, res, next)
  })
app.use('/data/g/:owner/:repo/*', (req, res, next) => {
    const owner = req.params.owner
    const repo = req.params.repo
    const filename = req.params[0]
    req.url = filename
    express.static(path.join(getGameDir(owner,repo),".lake","gamedata"))(req, res, next)
  })
app.use('/', router)

let server
if (crtFile && keyFile) {
  var privateKey  = fs.readFileSync(keyFile, 'utf8')
  var certificate = fs.readFileSync(crtFile, 'utf8')
  var credentials = {key: privateKey, cert: certificate}

  const PORT = process.env.PORT ?? 443
  server = https.createServer(credentials, app).listen(PORT,
    () => console.log(`HTTPS on port ${PORT}`))

  // redirect http to https
  express().get('*', function(req, res) {
    res.redirect('https://' + req.headers.host + req.url).listen(80)
  })
} else {
  const PORT = process.env.PORT ?? 8080
  server = app.listen(PORT,
    () => console.log(`HTTP on port ${PORT}`))
}

const wss = new WebSocketServer({ server })

/** We keep queues of started Lean Server processes to be ready when a user arrives */
const queue = {}

function getTag(owner, repo) {
  return `g/${owner.toLowerCase()}/${repo.toLowerCase()}`
}

function getGameDir(owner, repo) {
  owner = owner.toLowerCase()
  if (owner == 'local') {
    if(!isDevelopment) {
      console.error(`No local games in production mode.`)
      return ""
    }
  } else {
    if(!fs.existsSync(path.join(__dirname, '..', 'games'))) {
      console.error(`Did not find the following folder: ${path.join(__dirname, '..', 'games')}`)
      console.error('Did you already import any games?')
      return ""
    }
  }

  let game_dir = (owner == 'local') ?
    // note: in the local case we need `repo` to be case sensitive
    path.join(__dirname, '..', '..', repo) :
    path.join(__dirname, '..', 'games', `${owner}`, `${repo.toLowerCase()}`)

  if(!fs.existsSync(game_dir)) {
    console.error(`Game '${game_dir}' does not exist!`)
    return ""
  }

  return game_dir
}

function startServerProcess(owner, repo) {
  let game_dir = getGameDir(owner, repo)
  if (!game_dir) { return }

  let serverProcess
  if (isDevelopment) {
    console.warn("Running without Bubblewrap container!")

    // TODO: use the gameserver
    // serverProcess = cp.spawn("lean", ["--server"], { cwd: game_dir })

    let args = ["--server", game_dir]
    let binDir = path.join(game_dir, ".lake", "packages", "GameServer", "server", ".lake", "build", "bin")
    // Note: `cwd` is important to be the `bin` directory as `Watchdog` calls `./gameserver` again
    if (fs.existsSync(binDir)) {
      // Try to use the game's own copy of `gameserver`.
      serverProcess = cp.spawn("./gameserver", args, { cwd: binDir })
    } else {
      // If the game is built with `-Klean4game.local` there is no copy in the lake packages.
      serverProcess = cp.spawn("./gameserver", args,
        { cwd: path.join(__dirname, "..", "server", ".lake", "build", "bin") })
    }
  } else {
    console.info("Running with Bubblewrap container.")
    serverProcess =  cp.spawn(
      "./bubblewrap.sh",
      [ game_dir, path.join(__dirname, '..')],
      { cwd: __dirname }
    )
  }

  serverProcess.stderr.on('data', data =>
    console.error(`Lean Server: ${data}`)
  )
  serverProcess.on('error', error =>
    console.error(`Launching Lean Server failed: ${error}`)
  )
  serverProcess.on('close', (code, _signal) => {
    console.log(`Lean server exited with code ${code}`)
  })

  return serverProcess
}

/** start Lean Server processes to refill the queue */
function fillQueue(tag) {
  while (queue[tag].length < queueLength[tag]) {
    let serverProcess
    serverProcess = startServerProcess(tag)
    if (serverProcess == null) {
      console.error('serverProcess was undefined/null')
      return
    }
    queue[tag].push(serverProcess)
  }
}

// // TODO: We disabled queue for now
// if (!isDevelopment) { // Don't use queue in development
//   for (let tag in queueLength) {
//     queue[tag] = []
//     fillQueue(tag)
//   }
// }

wss.addListener("connection", function(ws, req) {
  // server expects URL of the form `/websocket/g/{owner}/{repo}`
  const urlRegEx = /^\/websocket\/g\/([\w.-]+)\/([\w.-]+)\/?$/
  const reRes = urlRegEx.exec(req.url)
  if (!reRes) { console.error(`Connection refused because of invalid URL: ${req.url}`); return }
  const owner = reRes[1]
  const repo = reRes[2]
  const tag = getTag(owner, repo)

  const ip = anonymize(req.headers['x-forwarded-for'] || req.socket.remoteAddress)
  let ps
  if (!queue[tag] || queue[tag].length == 0) {
    ps = startServerProcess(owner, repo)
  } else {
    console.info('Got process from the queue')
    ps = queue[tag].shift() // Pick the first Lean process; it's likely to be ready immediately
    // TODO
    // async () => {
    //   fillQueue(tag)
    // }
  }
  if (ps == null) {
    console.error('server process is undefined/null')
    return
  }

  const socket = {
    onMessage: (cb) => { ws.on("message", cb) },
    onError: (cb) => { ws.on("error", cb) },
    onClose: (cb) => { ws.on("close", cb) },
    send: (data, cb) => { ws.send(data,cb) }
  }
  const reader = new rpc.WebSocketMessageReader(socket)
  const writer = new rpc.WebSocketMessageWriter(socket)
  const socketConnection = jsonrpcserver.createConnection(reader, writer, () => ws.close())
  const serverConnection = jsonrpcserver.createProcessStreamConnection(ps)
  socketConnection.forward(serverConnection, message => {
    if (isDevelopment) {
      console.log(`CLIENT: ${JSON.stringify(message)}`)
    }
    return message
  })
  serverConnection.forward(socketConnection, message => {
    if (isDevelopment) {
      console.log(`SERVER: ${JSON.stringify(message)}`)
    }
    return message
  })

  ws.on('close', () => {
    console.log(`[${new Date()}] Socket closed - ${ip}`)
    socketCounter -= 1
  })

  socketConnection.onClose(() => serverConnection.dispose())
  serverConnection.onClose(() => socketConnection.dispose())

  console.log(`[${new Date()}] Socket opened - ${ip}`)
  socketCounter += 1
  logStats()
})
