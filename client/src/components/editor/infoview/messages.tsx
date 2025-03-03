import * as React from 'react'
import fastIsEqual from 'react-fast-compare'
import {
    Diagnostic,
    DiagnosticSeverity,
    DocumentUri,
    Location,
    PublishDiagnosticsParams,
} from 'vscode-languageserver-protocol'

import { LeanDiagnostic, RpcErrorCode } from '@leanprover/infoview-api'

import { getInteractiveDiagnostics, InteractiveDiagnostic } from '@leanprover/infoview-api'
import { Details } from './collapsing'
import { ConfigContext, EditorContext, EnvPosContext, LspDiagnosticsContext } from './contexts'
import { RpcContext, useRpcSessionAtPos } from './rpcSessions'
import { InteractiveMessage } from './traceExplorer'
import {
    addUniqueKeys,
    basename,
    DocumentPosition,
    escapeHtml,
    Keyed,
    useEvent,
    usePausableState,
    useServerNotificationState,
} from './util'

interface MessageViewProps {
    uri: DocumentUri
    diag: InteractiveDiagnostic
}

const MessageView = React.memo(({ uri, diag }: MessageViewProps) => {
    const ec = React.useContext(EditorContext)
    const fname = escapeHtml(basename(uri))
    const { line, character } = diag.range.start
    const loc: Location = { uri, range: diag.range }
    /* We grab the text contents of the message from `node.innerText`. */
    const node = React.useRef<HTMLDivElement>(null)
    const severityClass = diag.severity
        ? {
              [DiagnosticSeverity.Error]: 'error',
              [DiagnosticSeverity.Warning]: 'warning',
              [DiagnosticSeverity.Information]: 'information',
              [DiagnosticSeverity.Hint]: 'hint',
          }[diag.severity]
        : ''
    const title = `${fname}:${line + 1}:${character}`
    const startPos: DocumentPosition = React.useMemo(
        () => ({ uri, ...(diag.fullRange?.start || diag.range.start) }),
        [uri, diag.fullRange, diag.range],
    )
    return (
        <Details initiallyOpen>
            <span className={severityClass}>
                {title}
                <span className="fr" onClick={e => e.preventDefault()}>
                    <a
                        className="link pointer mh2 dim codicon codicon-go-to-file"
                        onClick={_ => {
                            void ec.revealLocation(loc)
                        }}
                        title="reveal file location"
                    ></a>
                    <a
                        className="link pointer mh2 dim codicon codicon-quote"
                        data-id="copy-to-comment"
                        onClick={_ => {
                            if (node.current) void ec.copyToComment(node.current.innerText)
                        }}
                        title="copy message to comment"
                    ></a>
                    <a
                        className="link pointer mh2 dim codicon codicon-clippy"
                        onClick={_ => {
                            if (node.current) void ec.api.copyToClipboard(node.current.innerText)
                        }}
                        title="copy message to clipboard"
                    ></a>
                </span>
            </span>
            <div className="ml1" ref={node}>
                <pre className="font-code pre-wrap">
                    <EnvPosContext.Provider value={startPos}>
                        <InteractiveMessage fmt={diag.message} />
                    </EnvPosContext.Provider>
                </pre>
            </div>
        </Details>
    )
}, fastIsEqual)

function mkMessageViewProps(uri: DocumentUri, messages: InteractiveDiagnostic[]): Keyed<MessageViewProps>[] {
    const views: MessageViewProps[] = messages
        .sort((msga, msgb) => {
            const a = msga.fullRange?.end || msga.range.end
            const b = msgb.fullRange?.end || msgb.range.end
            return a.line === b.line ? a.character - b.character : a.line - b.line
        })
        .map(m => {
            return { uri, diag: m }
        })

    return addUniqueKeys(views, v => DocumentPosition.toString({ uri: v.uri, ...v.diag.range.start }))
}

/** Shows the given messages assuming they are for the given file. */
export const MessagesList = React.memo(({ uri, messages }: { uri: DocumentUri; messages: InteractiveDiagnostic[] }) => {
    const should_hide = messages.length === 0
    if (should_hide) {
        return <>No messages.</>
    }

    return (
        <div className="ml1">
            {mkMessageViewProps(uri, messages).map(m => (
                <MessageView {...m} key={m.key} />
            ))}
        </div>
    )
})

function lazy<T>(f: () => T): () => T {
    let state: { t: T } | undefined
    return () => {
        if (!state) state = { t: f() }
        return state.t
    }
}

/** Displays all messages for the specified file. Can be paused. */
export function AllMessages({ uri: uri0 }: { uri: DocumentUri }) {
    const ec = React.useContext(EditorContext)
    const rs0 = useRpcSessionAtPos({ uri: uri0, line: 0, character: 0 })
    const dc = React.useContext(LspDiagnosticsContext)
    const config = React.useContext(ConfigContext)
    const diags0 = React.useMemo(() => dc.get(uri0) || [], [dc, uri0])

    const iDiags0 = React.useMemo(
        () =>
            lazy(async () => {
                // The last line for which we have received diagnostics so far.
                // Providing a line range to `getInteractiveDiagnostics`
                // ensures that the call doesn't block until the whole file is elaborated.
                const maxLine = diags0.reduce((ln, d) => Math.max(ln, d.range.end.line), 0) + 1
                try {
                    const diags = await getInteractiveDiagnostics(rs0, { start: 0, end: maxLine })
                    if (diags.length > 0) {
                        return diags
                    }
                } catch (err: any) {
                    if (err?.code === RpcErrorCode.ContentModified) {
                        // Document has been changed since we made the request. This can happen
                        // while typing quickly. When the server catches up on next edit, it will
                        // send new diagnostics to which the infoview responds by calling
                        // `getInteractiveDiagnostics` again.
                    } else {
                        console.log('getInteractiveDiagnostics error ', err)
                    }
                }
                return diags0.map(d => ({ ...(d as LeanDiagnostic), message: { text: d.message } }))
            }),
        [rs0, diags0],
    )
    const [{ isPaused, setPaused }, [uri, rs, diags, iDiags], _] = usePausableState(false, [uri0, rs0, diags0, iDiags0])

    // Fetch interactive diagnostics when we're entering the paused state
    // (if they haven't already been fetched before)
    React.useEffect(() => {
        if (isPaused) {
            void iDiags()
        }
    }, [iDiags, isPaused])

    const setOpenRef = React.useRef<React.Dispatch<React.SetStateAction<boolean>>>()
    useEvent(
        ec.events.requestedAction,
        _ => {
            if (setOpenRef.current !== undefined) {
                setOpenRef.current(t => !t)
            }
        },
        [setOpenRef],
        'toggleAllMessages',
    )

    // The number of actually displayed messages, or `undefined` if the panel is collapsed.
    // When `undefined`, we can approximate it by `diags.length`.
    const [numDiags, setNumDiags] = React.useState<number | undefined>(undefined)

    return (
        <RpcContext.Provider value={rs}>
            <Details setOpenRef={r => (setOpenRef.current = r)} initiallyOpen={!config.autoOpenShowsGoal}>
                <>
                    All Messages ({numDiags ?? diags.length})
                    <span
                        className="fr"
                        onClick={e => {
                            e.preventDefault()
                        }}
                    >
                        <a
                            className={
                                'link pointer mh2 dim codicon ' +
                                (isPaused ? 'codicon-debug-continue' : 'codicon-debug-pause')
                            }
                            onClick={_ => {
                                setPaused(p => !p)
                            }}
                            title={isPaused ? 'continue updating' : 'pause updating'}
                        ></a>
                    </span>
                </>
                <AllMessagesBody uri={uri} messages={iDiags} setNumDiags={setNumDiags} />
            </Details>
        </RpcContext.Provider>
    )
}

interface AllMessagesBodyProps {
    uri: DocumentUri
    messages: () => Promise<InteractiveDiagnostic[]>
    setNumDiags: React.Dispatch<React.SetStateAction<number | undefined>>
}

/** We factor out the body of {@link AllMessages} which lazily fetches its contents only when expanded. */
function AllMessagesBody({ uri, messages, setNumDiags }: AllMessagesBodyProps) {
    const [msgs, setMsgs] = React.useState<InteractiveDiagnostic[] | undefined>(undefined)
    React.useEffect(() => {
        const fn = async () => {
            const msgs = await messages()
            setMsgs(msgs)
            setNumDiags(msgs.length)
        }
        void fn()
    }, [messages, setNumDiags])
    React.useEffect(() => () => /* Called on unmount. */ setNumDiags(undefined), [setNumDiags])
    if (msgs === undefined) return <>Loading messages...</>
    else return <MessagesList uri={uri} messages={msgs} />
}

/**
 * Provides a `LspDiagnosticsContext` which stores the latest version of the
 * diagnostics as sent by the publishDiagnostics notification.
 */
export function WithLspDiagnosticsContext({ children }: React.PropsWithChildren<{}>) {
    const [allDiags, _0] = useServerNotificationState(
        'textDocument/publishDiagnostics',
        new Map<DocumentUri, Diagnostic[]>(),
        async (params: PublishDiagnosticsParams) => diags => new Map(diags).set(params.uri, params.diagnostics),
        [],
    )

    return <LspDiagnosticsContext.Provider value={allDiags}>{children}</LspDiagnosticsContext.Provider>
}

/** Embeds a non-interactive diagnostic into the type `InteractiveDiagnostic`. */
export function lspDiagToInteractive(diag: Diagnostic): InteractiveDiagnostic {
    return { ...(diag as LeanDiagnostic), message: { text: diag.message } }
}
