import { WebSocketServer } from 'ws';
import express from 'express'
import path from 'path'
import * as cp from 'child_process';
import * as url from 'url';
import * as rpc from 'vscode-ws-jsonrpc';
import * as jsonrpcserver from 'vscode-ws-jsonrpc/server';
import os from 'os';
import anonymize from 'ip-anonymize';
import { importTrigger, importStatus } from './import.mjs'
// import fs from 'fs'

/**
 * IMPORTANT! Tags here need to be lower case!
*/
const games = {
    "g/hhu-adam/robo": {
        dir: "Robo",
        queueLength: 5
    },
    "g/hhu-adam/nng4": {
        dir: "NNG4",
        queueLength: 5
    },
    "g/djvelleman/stg4": {
        dir: "STG4",
        queueLength: 5
    },
    "g/hhu-adam/nng4-old": {
        dir: "NNG4-OLD",
        queueLength: 0
    }
}

const __filename = url.fileURLToPath(import.meta.url);
const __dirname = url.fileURLToPath(new URL('.', import.meta.url));

const app = express()

const PORT = process.env.PORT || 8080;

var router = express.Router();

router.get('/import/status/:owner/:repo', importStatus)
router.get('/import/trigger/:owner/:repo', importTrigger)

const server = app
  .use(express.static(path.join(__dirname, '../client/dist/')))
  .use('/', router)
  .listen(PORT, () => console.log(`Listening on ${PORT}`));

const wss = new WebSocketServer({ server })

var socketCounter = 0

const environment = process.env.NODE_ENV
const isDevelopment = environment === 'development'

/** We keep queues of started Lean Server processes to be ready when a user arrives */
const queue = {}

function tag(owner, repo) {
  return `g/${owner.toLowerCase()}/${repo.toLowerCase()}`
}

function startServerProcess(owner, repo) {
  let game_dir = (owner == 'local') ?
    repo : games[tag(owner, repo)]?.dir

  if (owner == 'local') {
    if(!isDevelopment) {
      console.error(`No local games in production mode.`)
      return
    }
    // TODO: This test does not work
    // if (!fs.existsSync(path.join("../", game_dir))) {
    //   console.error(`Game folder does not exists: ${game_dir}`)
    //   return
    // }
  }

  if (!game_dir) {
    console.error(`Unknown game: ${tag(owner, repo)}`)
    return
  }

  let serverProcess
  if (isDevelopment) {
    let args = ["--server", path.join('..','..','games',`${owner}`,`${repo}`)]
    serverProcess = cp.spawn("./gameserver", args,
        { cwd: path.join(__dirname, "./build/bin/") })
  } else {
    serverProcess =  cp.spawn("./bubblewrap.sh",
      [game_dir],
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
function fillQueue(owner, repo) {
    while (queue[tag(owner, repo)].length < games[tag(owner, repo)].queueLength) {
      const serverProcess = startServerProcess(tag(owner, repo))
      queue[tag(owner, repo)].push(serverProcess)
    }
}

// if (!isDevelopment) { // Don't use queue in development
//   for (let tag in games) {
//     queue[tag] = []
//     fillQueue(tag)
//   }
// }

const urlRegEx = /^\/websocket\/g\/([\w.-]+)\/([\w.-]+)$/

wss.addListener("connection", function(ws, req) {
    const reRes = urlRegEx.exec(req.url)
    if (!reRes) { console.error(`Connection refused because of invalid URL: ${req.url}`); return; }
    const owner = reRes[1]
    const repo = reRes[2]
    // const tag = `g/${owner.toLowerCase()}/${repo.toLowerCase()}`

    // // TODO
    // if (isDevelopment && process.env.DEV_CONTAINER) {
    //     tag = `g/local/game`
    // }

    let ps;
    if (!queue[tag(owner, repo)] || queue[tag(owner, repo)].length == 0) {
        ps = startServerProcess(owner, repo)
    } else {
        ps = queue[tag(owner, repo)].shift() // Pick the first Lean process; it's likely to be ready immediately
        fillQueue(owner, repo)
    }

    socketCounter += 1;
    const ip = anonymize(req.headers['x-forwarded-for'] || req.socket.remoteAddress)
    console.log(`[${new Date()}] Socket opened - ${ip}`)

    const socket = {
        onMessage: (cb) => { ws.on("message", cb) },
        onError: (cb) => { ws.on("error", cb) },
        onClose: (cb) => { ws.on("close", cb) },
        send: (data, cb) => { ws.send(data,cb) }
    }
    const reader = new rpc.WebSocketMessageReader(socket);
    const writer = new rpc.WebSocketMessageWriter(socket);
    const socketConnection = jsonrpcserver.createConnection(reader, writer, () => ws.close())
    const serverConnection = jsonrpcserver.createProcessStreamConnection(ps);
    socketConnection.forward(serverConnection, message => {
        if (isDevelopment) {console.log(`CLIENT: ${JSON.stringify(message)}`)}
        return message;
    });
    serverConnection.forward(socketConnection, message => {
      if (isDevelopment) {console.log(`SERVER: ${JSON.stringify(message)}`)}
        return message;
    });

    console.log(`[${new Date()}] Number of open sockets - ${socketCounter}`)
    console.log(`[${new Date()}] Free RAM - ${Math.round(os.freemem() / 1024 / 1024)} / ${Math.round(os.totalmem() / 1024 / 1024)} MB`)

    ws.on('close', () => {
      console.log(`[${new Date()}] Socket closed - ${ip}`)
      socketCounter -= 1;
    })

    socketConnection.onClose(() => serverConnection.dispose());
    serverConnection.onClose(() => socketConnection.dispose());
})
