const WebSocket = require("ws");
const express = require("express");
const app = express()
const path = require("path")
const { spawn } = require('child_process');

const PORT = process.env.PORT || 8080;

const server = app
  .use(express.static(path.join(__dirname, '../client/dist/')))
  .listen(PORT, () => console.log(`Listening on ${PORT}`));

const wss = new WebSocket.Server({ server })

const environment = process.env.NODE_ENV
const isDevelopment = environment === 'development'

let cmd, cmdArgs;
if (isDevelopment) {
    cmd = "./leanserver/build/bin/gameserver";
    cmdArgs = ["TestGame","testgame"];
} else{
    cmd = "docker";
    cmdArgs = ["run", "--runtime=runsc", "--network=none", "--rm", "-i", "testgame:latest"];
}

class ClientConnection {

    content = Buffer.alloc(0)

    constructor(ws){
        console.log("Socket opened.")
        this.ws = ws    
        this.ws.send("ok");

        this.ws.on("message", (msg) => {
            this.send(JSON.parse(msg.toString("utf8")));
        })

        this.ws.on("close", () => {
            this.lean.kill();
            console.log("Socket closed.")
        })

        this.lean = spawn(cmd, cmdArgs);

        this.lean.stdout.on('readable', () => {
            this.read();
        });

        this.lean.stderr.on('data', (data) => {
            console.error(`stderr: ${data}`);
        });
    }

    read () {
        let chr;
        while (chr = this.lean.stdout.read(1)) {
            this.content = Buffer.concat([this.content,chr])
            if (chr.toString() == "\n") {
                console.log(this.content.toString())
                this.ws.send(this.content.toString());
                this.content = Buffer.alloc(0)
            }
        }
    }

    send(data) {
        const str = JSON.stringify(data) + "\n";
        const byteLength = Buffer.byteLength(str, "utf-8");
    
        this.lean.stdin.cork();
        this.lean.stdin.write(str);
        this.lean.stdin.uncork();
    }
}

wss.on("connection", function(ws) {    // what should a websocket do on connection
    new ClientConnection(ws)
})

// server.on('upgrade', async function upgrade(request, socket, head) {
//     wss.handleUpgrade(request, socket, head, function done(ws) {
//         wss.emit('connection', ws, request);
//     });
// });