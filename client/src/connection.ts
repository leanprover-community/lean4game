/**
 *  @fileOverview todo
 */

import * as React from 'react';
import { LeanClient } from 'lean4web/client/src/editor/leanclient';
import { IConnectionProvider } from 'monaco-languageclient'
import { toSocket, WebSocketMessageReader, WebSocketMessageWriter } from 'vscode-ws-jsonrpc'

export class Connection {
  private game: string = undefined // We only keep a connection to a single game at a time
  private leanClient: LeanClient = null

  getLeanClient(game): LeanClient {
    if (this.game !== game) {
      if (this.leanClient) {
        this.leanClient.stop() // Stop previous Lean client
      }
      this.game = game
      // Start a new Lean client for the new `gameId`.
      const socketUrl = ((window.location.protocol === "https:") ? "wss://" : "ws://") + window.location.host + '/websocket/' + game

      const connectionProvider : IConnectionProvider = {
        get: async () => {
          return await new Promise((resolve, reject) => {
            console.log(`connecting ${socketUrl}`)
            const websocket = new WebSocket(socketUrl)
            websocket.addEventListener('error', (ev) => {
              reject(ev)
            })
            websocket.addEventListener('message', (msg) => {
              // console.log(msg.data)
            })
            websocket.addEventListener('open', () => {
              const socket = toSocket(websocket)
              const reader = new WebSocketMessageReader(socket)
              const writer = new WebSocketMessageWriter(socket)
              resolve({
                reader,
                writer
              })
            })
          })
        }
      }

      this.leanClient = new LeanClient(connectionProvider, () => {})
    }

    return this.leanClient
  }

  /** If not already started, starts the Lean client. resolves the returned promise as soon as a
   * Lean client is running.
   */
  startLeanClient = (game) => {
    return new Promise<LeanClient>((resolve) => {
      const leanClient = this.getLeanClient(game)
      if (leanClient.isRunning()) {
        resolve(leanClient)
      } else {
        if (!leanClient.isStarted()) {
          leanClient.start()
        }
        leanClient.restarted(() => {
          // This keep alive message is not recognized by the server,
          // but it makes sure that the websocket connection does not
          // time out after 60 seconds.
          setInterval(() => {leanClient.sendNotification('$/keepAlive', {}) }, 5000)
          resolve(leanClient)
        })
      }
    })
  }
}

export const connection = new Connection()

export const ConnectionContext = React.createContext(null);

export const useLeanClient = (gameId) => {
  const leanClient = connection.getLeanClient(gameId)
  const [leanClientStarted, setLeanClientStarted] = React.useState(leanClient.isStarted())

  React.useEffect(() => {
    const t1 = leanClient.restarted(() => { console.log("START"); setLeanClientStarted(true) })
    const t2 = leanClient.stopped(() => { console.log("STOP"); setLeanClientStarted(false) })

    return () => {t1.dispose(); t2.dispose()}
  }, [leanClient, setLeanClientStarted])

  return {leanClientStarted, leanClient}
}
