
import * as monaco from 'monaco-editor/esm/vs/editor/editor.api.js'
import { LeanClient } from 'lean4web/client/src/editor/leanclient';
import * as React from 'react';


export class Connection {
  private leanClient = null

  getLeanClient() {
    if (this.leanClient === null) {
      const socketUrl = ((window.location.protocol === "https:") ? "wss://" : "ws://") + window.location.host + '/websocket/'

      const uri = monaco.Uri.parse('file:///')
      this.leanClient = new LeanClient(socketUrl, undefined, uri, () => {})
    }

    return this.leanClient
  }

  /** Call `callback` when the leanClient has started. If not already started, start it. */
  whenLeanClientStarted = (callback) => {
    const leanClient = this.getLeanClient()
    if (leanClient.isRunning()) {
      callback(leanClient)
    } else {
      if (!leanClient.isStarted()) {
        leanClient.start()
      }
     leanClient.restarted(() => { callback(leanClient) })
    }
  }
}

export const connection = new Connection()

export const ConnectionContext = React.createContext(null);
