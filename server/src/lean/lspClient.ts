import type { ChildProcessWithoutNullStreams } from 'node:child_process'

import {
  createMessageConnection,
  type MessageConnection,
} from 'vscode-jsonrpc/node'

export interface LspClient {
  request<R>(method: string, params: unknown): Promise<R>
  notify(method: string, params: unknown): Promise<void>
  onNotification(method: string, handler: (params: any) => void): void
}

/** Wraps a `lake serve` child process's stdio in a minimal LSP client. */
export function createLspClient(
  child: ChildProcessWithoutNullStreams,
): LspClient {
  const connection: MessageConnection = createMessageConnection(
    child.stdout,
    child.stdin,
  )
  connection.listen()

  return {
    request: (method, params) => connection.sendRequest(method, params),
    notify: (method, params) => connection.sendNotification(method, params),
    onNotification: (method, handler) => {
      connection.onNotification(method, handler)
    },
  }
}
