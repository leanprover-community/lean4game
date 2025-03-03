import { RpcCallParams, RpcReleaseParams, RpcSessionAtPos, RpcSessions } from '@leanprover/infoview-api'
import * as React from 'react'
import type {
    DidCloseTextDocumentParams,
    DocumentUri,
    TextDocumentPositionParams,
} from 'vscode-languageserver-protocol'
import { EditorContext, EnvPosContext } from './contexts'
import { DocumentPosition, useClientNotificationEffect, useEvent } from './util'

const RpcSessionsContext = React.createContext<RpcSessions | undefined>(undefined)

/**
 * Provides a {@link RpcSessionsContext} to the children.
 * The {@link RpcSessions} object stored there manages RPC sessions in the Lean server.
 */
export function WithRpcSessions({ children }: { children: React.ReactNode }) {
    const ec = React.useContext(EditorContext)
    const [sessions] = React.useState<RpcSessions>(
        () =>
            new RpcSessions({
                createRpcSession: (uri: DocumentUri) => ec.api.createRpcSession(uri),
                closeRpcSession: (uri: DocumentUri) => ec.api.closeRpcSession(uri),
                call: (params: RpcCallParams) =>
                    ec.api.sendClientRequest(params.textDocument.uri, '$/lean/rpc/call', params),
                release: (params: RpcReleaseParams) =>
                    void ec.api.sendClientNotification(params.uri, '$/lean/rpc/release', params),
            }),
    )
    React.useEffect(() => {
        // Clean up the sessions on unmount
        return () => sessions.dispose()
    }, [sessions])

    useClientNotificationEffect(
        'textDocument/didClose',
        (params: DidCloseTextDocumentParams) => {
            sessions.closeSessionForFile(params.textDocument.uri)
        },
        [sessions],
    )

    // TODO: only restart files for the server that stopped
    useEvent(ec.events.serverRestarted, () => sessions.closeAllSessions())

    return <RpcSessionsContext.Provider value={sessions}>{children}</RpcSessionsContext.Provider>
}

const noCtxRpcSession: RpcSessionAtPos = {
    call: async () => {
        throw new Error('no RPC context set')
    },
}

const noPosRpcSession: RpcSessionAtPos = {
    call: async () => {
        throw new Error('no position context set')
    },
}

export function useRpcSessionAtTdpp(pos: TextDocumentPositionParams): RpcSessionAtPos {
    return React.useContext(RpcSessionsContext)?.connect(pos) || noCtxRpcSession
}

export function useRpcSessionAtPos(pos: DocumentPosition): RpcSessionAtPos {
    return useRpcSessionAtTdpp(DocumentPosition.toTdpp(pos))
}

/** @deprecated use {@link useRpcSession} instead */
/*
 * NOTE(WN): This context cannot be removed as of 2024-05-27 since existing widgets use it.
 * For backwards compatibility, it must be set to the correct value by infoview code.
 * A future major release of @leanprover/infoview could remove this context
 * after it has been deprecated for a sufficiently long time.
 */
export const RpcContext = React.createContext<RpcSessionAtPos>(noCtxRpcSession)

/**
 * Retrieve an RPC session at {@link EnvPosContext},
 * if the context is set.
 * Otherwise return a dummy session that throws on any RPC call.
 */
export function useRpcSession(): RpcSessionAtPos {
    const pos = React.useContext(EnvPosContext)
    const rsc = React.useContext(RpcSessionsContext)
    if (!pos) return noPosRpcSession
    if (!rsc) return noCtxRpcSession
    return rsc.connect(DocumentPosition.toTdpp(pos))
}
