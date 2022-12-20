
import * as monaco from 'monaco-editor/esm/vs/editor/editor.api.js'
import { LeanClient } from 'lean4web/client/src/editor/leanclient';
import * as React from 'react';
import { useState } from 'react';


export class Connection {
  private leanClient = null

  getLeanClient(): LeanClient {
    if (this.leanClient === null) {
      const socketUrl = ((window.location.protocol === "https:") ? "wss://" : "ws://") + window.location.host + '/websocket/'

      const uri = monaco.Uri.parse('file:///')
      this.leanClient = new LeanClient(socketUrl, undefined, uri, () => {})
    }

    return this.leanClient
  }

  /** If not already started, starts the Lean client. resolves the returned promise as soon as a
   * Lean client is running.
   */
  startLeanClient = () => {
    return new Promise<LeanClient>((resolve) => {
      const leanClient = this.getLeanClient()
      if (leanClient.isRunning()) {
        resolve(leanClient)
      } else {
        if (!leanClient.isStarted()) {
          leanClient.start()
        }
        leanClient.restarted(() => { resolve(leanClient) })
      }
    })
  }
}

export const connection = new Connection()

export const ConnectionContext = React.createContext(null);

export const useLeanClient = () => {
  const leanClient = connection.getLeanClient()
  const [leanClientStarted, setLeanClientStarted] = useState(leanClient.isStarted())
  leanClient.restarted(() => { setLeanClientStarted(true) })
  // TODO handle stopping lean client
  return {leanClientStarted, leanClient}
}
