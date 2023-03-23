
import * as monaco from 'monaco-editor/esm/vs/editor/editor.api.js'
import { LeanClient } from 'lean4web/client/src/editor/leanclient';
import * as React from 'react';
import { useState } from 'react';


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
      const uri = monaco.Uri.parse('file:///')
      this.leanClient = new LeanClient(socketUrl, undefined, uri, () => {})
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
  const [leanClientStarted, setLeanClientStarted] = useState(leanClient.isStarted())

  React.useEffect(() => {
    const t1 = leanClient.restarted(() => { console.log("START"); setLeanClientStarted(true) })
    const t2 = leanClient.stopped(() => { console.log("STOP"); setLeanClientStarted(false) })

    return () => {t1.dispose(); t2.dispose()}
  }, [leanClient, setLeanClientStarted])

  return {leanClientStarted, leanClient}
}
