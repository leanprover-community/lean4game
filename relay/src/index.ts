import { WebSocketServer } from 'ws';
import express from 'express'
import path from 'path'
import * as cp from 'child_process';
import * as url from 'url';
import * as rpc from 'vscode-ws-jsonrpc';
import * as jsonrpcserver from 'vscode-ws-jsonrpc/server';
import os from 'os';
import fs from 'fs';
import anonymize from 'ip-anonymize';
import { importTrigger, importStatus } from './import.js'
import { logAccess } from './middleware.js';
import process from 'process';
import { spawn } from 'child_process'
// import fs from 'fs'

type Tag = {owner: string, repo: string}

/**
 * Add a game here if the server should keep a queue of pre-loaded games ready at all times.
 *
 * IMPORTANT! Tags here need to be lower case!
*/
const queueLength = {
  "g/hhu-adam/robo": 2,
  "g/leanprover-community/nng4": 5,
  "g/djvelleman/stg4": 2,
  "g/trequetrum/lean4game-logic": 2,
}

const __filename = url.fileURLToPath(import.meta.url);
const __dirname = url.fileURLToPath(new URL('.', import.meta.url));

const app = express()

const PORT = process.env.PORT || 8080;

var router = express.Router();

router.get('/import/status/:owner/:repo', importStatus)
router.get('/import/trigger/:owner/:repo', importTrigger)

const clientDistPath = path.join(__dirname, '..', '..', '..', 'client', 'dist');
const server = app
  .use(express.static(clientDistPath)) // TODO: add a dist folder from inside the game
  .use('/i18n/g/:owner/:repo/:lang/*', (req, res, next) => {
    const { owner, repo, lang } = logAccess(req);
    const filename = req.params[0];
    req.url = filename;
    express.static(path.join(getGameDir(owner,repo),".i18n",lang))(req, res, next);
  })
  .use('/data/g/:owner/:repo/*', (req, res, next) => {
    const owner = req.params.owner;
    const repo = req.params.repo
    const filename = req.params[0];
    req.url = filename;
    express.static(path.join(getGameDir(owner,repo),".lake","gamedata"))(req, res, next);
  })
  .use('/data/stats', (req, res, next) => {
    const statsScriptPath = path.join(__dirname, "..", "..", "scripts", "stats.sh");
    const statsProcess = spawn('/bin/bash', [statsScriptPath, process.pid.toString()])
    let outputData = ''
    let errorData = ''
    statsProcess.stdout.on('data', (data) => {
      outputData += data.toString();
    })
    statsProcess.stderr.on('data', (data) => {
      errorData += data.toString();
    })
    statsProcess.on('close', (code) => {
      if (code === 0) {
        res.send(outputData);
      } else {
        res.status(500).send(`Error executing script: ${errorData}`)
        console.error(`stats.sh exited with code ${code}. Error: ${errorData}`)
      }
    })
  })
  .use('/', router)
  .listen(PORT, () => console.log(`Listening on ${PORT}`));

const wss = new WebSocketServer({ server })

var socketCounter = 0

const environment = process.env.NODE_ENV
const isDevelopment = environment === 'development'

/** We keep queues of started Lean Server processes to be ready when a user arrives */
const queue = {}

function getTagString(tag: Tag) {
  return `g/${tag.owner.toLowerCase()}/${tag.repo.toLowerCase()}`
}

function getGameDir(owner, repo) {
  owner = owner.toLowerCase()
  if (owner == 'local') {
    if(!isDevelopment) {
      console.error(`No local games in production mode.`)
      return ""
    }
  } else {
    const gamesPath = path.join(__dirname, '..', '..', '..', 'games');
    if(!fs.existsSync(gamesPath)) {
      console.error(`Did not find the following folder: ${gamesPath}`)
      console.error('Did you already import any games?')
      return ""
    }
  }

  const gamePath = path.join(__dirname, '..', '..', '..', 'games', `${owner}`, `${repo.toLowerCase()}`);
  let game_dir = (owner == 'local') ?
    path.join(__dirname, '..', '..', repo) : // note: here we need `repo` to be case sensitive
    gamePath

  if(!fs.existsSync(game_dir)) {
    console.error(`Game '${game_dir}' does not exist!`)
    return ""
  }

  return game_dir;
}

function startServerProcess(owner, repo) {

  let game_dir = getGameDir(owner, repo)
  if (!game_dir) return;

  let serverProcess
  if (isDevelopment) {
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
    serverProcess =  cp.spawn("../../scripts/bubblewrap.sh",
      [ game_dir, path.join(__dirname, '..')],
      { cwd: __dirname })
  }

  serverProcess.on('error', error =>
    console.error(`Launching Lean Server failed: ${error}`)
  )
  if (serverProcess.stderr !== null) {
    serverProcess.stderr.on('data', data =>
      console.error(`Lean Server: ${data}`)
    )
  }
  return serverProcess
}

/** start Lean Server processes to refill the queue */
function fillQueue(tag: {owner: string, repo: string}) {
  const tagString = getTagString(tag)
  while (queue[tagString].length < queueLength[tagString]) {
    let serverProcess
    serverProcess = startServerProcess(tag.owner, tag.repo)
    if (serverProcess == null) {
      console.error('serverProcess was undefined/null')
      return
    }
    queue[tagString].push(serverProcess)
  }
}

// // TODO: We disabled queue for now
// if (!isDevelopment) { // Don't use queue in development
//   for (let tag in queueLength) {
//     queue[tag] = []
//     fillQueue(tag)
//   }
// }

const urlRegEx = /^\/websocket\/g\/([\w.-]+)\/([\w.-]+)$/

wss.addListener("connection", function(ws, req) {
    const reRes = urlRegEx.exec(req.url)
    if (!reRes) { console.error(`Connection refused because of invalid URL: ${req.url}`); return; }
    const reResTag: Tag = {owner: reRes[1], repo: reRes[2]}
    const owner = reResTag.owner
    const repo = reResTag.repo

    const tag = getTagString(reResTag)

    let ps
    if (!queue[tag] || queue[tag].length == 0) {
      ps = startServerProcess(owner, repo)
    } else {
        console.info('Got process from the queue')
        ps = queue[tag].shift() // Pick the first Lean process; it's likely to be ready immediately
        fillQueue(reResTag)
    }

    if (ps == null) {
      console.error('server process is undefined/null')
      return
    }

    socketCounter += 1;
    const ip = anonymize(req.headers['x-forwarded-for'] || req.socket.remoteAddress)

    // TODO (Matvey): extract further information from `req`, for example browser language.
    console.log(`[${new Date()}] Socket opened - ${ip} - ${owner}/${repo}`)

    const socket: rpc.IWebSocket = {
        onMessage: (cb) => { ws.on("message", cb) },
        onError: (cb) => { ws.on("error", cb) },
        onClose: (cb) => { ws.on("close", cb) },
        //send: (data, cb) => { ws.send(data, cb); }
        send: (data) => { ws.send(data); },
        dispose: () => {}
      }
    const reader = new rpc.WebSocketMessageReader(socket)
    const writer = new rpc.WebSocketMessageWriter(socket)
    const socketConnection = jsonrpcserver.createConnection(reader, writer, () => ws.close())
    const serverConnection = jsonrpcserver.createProcessStreamConnection(ps)
    socketConnection.forward(serverConnection, message => {
        if (isDevelopment) {console.log(`CLIENT: ${JSON.stringify(message)}`)}
        return message;
    })
    serverConnection.forward(socketConnection, message => {
      if (isDevelopment) {console.log(`SERVER: ${JSON.stringify(message)}`)}
        return message;
    });

    console.log(`[${new Date()}] Number of open sockets - ${socketCounter}`)
    console.log(`[${new Date()}] Free RAM - ${Math.round(os.freemem() / 1024 / 1024)} / ${Math.round(os.totalmem() / 1024 / 1024)} MB`)

    ws.on('close', () => {
      console.log(`[${new Date()}] Socket closed - ${ip}`)
      socketCounter -= 1
    })

    socketConnection.onClose(() => serverConnection.dispose())
    serverConnection.onClose(() => socketConnection.dispose())
})
