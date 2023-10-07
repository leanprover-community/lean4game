import * as React from 'react'
import fastIsEqual from 'react-fast-compare'
import { Location, DocumentUri, Diagnostic, DiagnosticSeverity, PublishDiagnosticsParams } from 'vscode-languageserver-protocol'

import { LeanDiagnostic, RpcErrorCode, getInteractiveDiagnostics, InteractiveDiagnostic, TaggedText_stripTags } from '@leanprover/infoview-api'

import { basename, escapeHtml, usePausableState, useEvent, addUniqueKeys, DocumentPosition, useServerNotificationState, useEventResult } from '../../../../node_modules/lean4-infoview/src/infoview/util'
import { ConfigContext, EditorContext, LspDiagnosticsContext, VersionContext } from '../../../../node_modules/lean4-infoview/src/infoview/contexts'
import { Details } from '../../../../node_modules/lean4-infoview/src/infoview/collapsing'
import { InteractiveMessage } from '../../../../node_modules/lean4-infoview/src/infoview/traceExplorer'
import { RpcContext, useRpcSessionAtPos } from '../../../../node_modules/lean4-infoview/src/infoview/rpcSessions'

import { InputModeContext } from './context'

interface MessageViewProps {
    uri: DocumentUri;
    diag: InteractiveDiagnostic;
}

/** A list of messages (info/warning/error) that are produced after this command */
function Error({error, typewriterMode} : {error : InteractiveDiagnostic, typewriterMode : boolean}) {
  // The first step will always have an empty command

  const severityClass = error.severity ? {
    [DiagnosticSeverity.Error]: 'error',
    [DiagnosticSeverity.Warning]: 'warning',
    [DiagnosticSeverity.Information]: 'information',
    [DiagnosticSeverity.Hint]: 'hint',
  }[error.severity] : '';

  const {line, character} = error.range.start;
  const title = `Line ${line+1}, Character ${character}`;

  // Hide "unsolved goals" messages
  let message;
  if ("append" in error.message && "text" in error.message.append[0] &&
  error.message?.append[0].text === "unsolved goals") {
      message = error.message.append[0]
  } else {
      message = error.message
  }

  return <div className={severityClass + ' ml1 message'}>
    {!typewriterMode && <p className="mv2">{title}</p>}
    <pre className="font-code pre-wrap">
      <InteractiveMessage fmt={message} />
    </pre>
  </div>
}

// TODO: Should not use index as key.
/** A list of messages (info/warning/error) that are produced after this command */
export function Errors ({errors, typewriterMode} : {errors : InteractiveDiagnostic[], typewriterMode : boolean}) {
  return <div>
    {errors.map((err, i) => (<Error key={`error-${i}`} error={err} typewriterMode={typewriterMode}/>))}
  </div>
}

const MessageView = React.memo(({uri, diag}: MessageViewProps) => {
    const ec = React.useContext(EditorContext);
    const fname = escapeHtml(basename(uri));
    const {line, character} = diag.range.start;
    const loc: Location = { uri, range: diag.range };
    const text = TaggedText_stripTags(diag.message);
    const severityClass = diag.severity ? {
        [DiagnosticSeverity.Error]: 'error',
        [DiagnosticSeverity.Warning]: 'warning',
        [DiagnosticSeverity.Information]: 'information',
        [DiagnosticSeverity.Hint]: 'hint',
    }[diag.severity] : '';
    const title = `Line ${line+1}, Character ${character}`;

    // Hide "unsolved goals" messages
    let message;
    if ("append" in diag.message && "text" in diag.message.append[0] &&
      diag.message?.append[0].text === "unsolved goals") {
        message = diag.message.append[0]
    } else {
        message = diag.message
    }

    const { typewriterMode } = React.useContext(InputModeContext)

    return (
    // <details open>
        // <summary className={severityClass + ' mv2 pointer'}>{title}
        //     <span className="fr">
        //         <a className="link pointer mh2 dim codicon codicon-go-to-file"
        //            onClick={e => { e.preventDefault(); void ec.revealLocation(loc); }}
        //            title="reveal file location"></a>
        //         <a className="link pointer mh2 dim codicon codicon-quote"
        //            data-id="copy-to-comment"
        //            onClick={e => {e.preventDefault(); void ec.copyToComment(text)}}
        //            title="copy message to comment"></a>
        //         <a className="link pointer mh2 dim codicon codicon-clippy"
        //            onClick={e => {e.preventDefault(); void ec.api.copyToClipboard(text)}}
        //            title="copy message to clipboard"></a>
        //     </span>
        // </summary>
        <div className={severityClass + ' ml1 message'}>
            {!typewriterMode && <p className="mv2">{title}</p>}
            <pre className="font-code pre-wrap">
                <InteractiveMessage fmt={message} />
            </pre>
        </div>
    // </details>
    )
}, fastIsEqual)

function mkMessageViewProps(uri: DocumentUri, messages: InteractiveDiagnostic[]): MessageViewProps[] {
    const views: MessageViewProps[] = messages
        .sort((msga, msgb) => {
            const a = msga.fullRange?.end || msga.range.end;
            const b = msgb.fullRange?.end || msgb.range.end;
            return a.line === b.line ? a.character - b.character : a.line - b.line
        }).map(m => {
            return { uri, diag: m };
        });

    return addUniqueKeys(views, v => DocumentPosition.toString({uri: v.uri, ...v.diag.range.start}));
}

/** Shows the given messages assuming they are for the given file. */
export const MessagesList = React.memo(({uri, messages}: {uri: DocumentUri, messages: InteractiveDiagnostic[]}) => {
    const should_hide = messages.length === 0;
    if (should_hide) { return <></> }

    return (
    <div>
        {mkMessageViewProps(uri, messages).map(m => <MessageView {...m} />)}
    </div>
    );
})

function lazy<T>(f: () => T): () => T {
    let state: {t: T} | undefined
    return () => {
        if (!state) state = {t: f()}
        return state.t
    }
}

/** Displays all messages for the specified file. Can be paused. */
export function AllMessages() {
    const ec = React.useContext(EditorContext);
    const sv = React.useContext(VersionContext);
    const curPos: DocumentPosition | undefined =
        useEventResult(ec.events.changedCursorLocation, loc => loc ? { uri: loc.uri, ...loc.range.start } : undefined)
    const rs0 = useRpcSessionAtPos({ uri: curPos.uri, line: 0, character: 0 });
    const dc = React.useContext(LspDiagnosticsContext);
    const config = React.useContext(ConfigContext);
    const diags0 = dc.get(curPos.uri) || [];

    const iDiags0 = React.useMemo(() => lazy(async () => {
        try {
            const diags = await getInteractiveDiagnostics(rs0);
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
        return diags0.map(d => ({ ...(d as LeanDiagnostic), message: { text: d.message } }));
    }), [sv, rs0, curPos.uri, diags0]);
    const [{ isPaused, setPaused }, [uri, rs, diags, iDiags], _] = usePausableState(false, [curPos.uri, rs0, diags0, iDiags0]);

    // Fetch interactive diagnostics when we're entering the paused state
    // (if they haven't already been fetched before)
    React.useEffect(() => { if (isPaused) { void iDiags() } }, [iDiags, isPaused]);

    const setOpenRef = React.useRef<React.Dispatch<React.SetStateAction<boolean>>>();
    useEvent(ec.events.requestedAction, act => {
        if (act.kind === 'toggleAllMessages' && setOpenRef.current !== undefined) {
            setOpenRef.current(t => !t);
        }
    });

    return (
    <RpcContext.Provider value={rs}>
    {/* <Details setOpenRef={setOpenRef as any} initiallyOpen={!config.autoOpenShowsGoal}>
        <summary className="mv2 pointer">
            All Messages ({diags.length})
            <span className="fr">
                <a className={'link pointer mh2 dim codicon ' + (isPaused ? 'codicon-debug-continue' : 'codicon-debug-pause')}
                   onClick={e => { e.preventDefault(); setPaused(p => !p); }}
                   title={isPaused ? 'continue updating' : 'pause updating'}>
                </a>
            </span>
        </summary> */}
        <AllMessagesBody uri={curPos.uri} key={curPos.uri} messages={iDiags0} />
    {/* </Details> */}
    </RpcContext.Provider>
    )
}

/** We factor out the body of {@link AllMessages} which lazily fetches its contents only when expanded. */
function AllMessagesBody({uri, messages}: {uri: DocumentUri, messages: () => Promise<InteractiveDiagnostic[]>}) {
    const [msgs, setMsgs] = React.useState<InteractiveDiagnostic[] | undefined>(undefined)
    React.useEffect(() => { void messages().then(setMsgs) }, [messages])
    if (msgs === undefined) return <div>Loading messages...</div>
    else return <MessagesList uri={uri} messages={msgs}/>
}

/**
 * Provides a `LspDiagnosticsContext` which stores the latest version of the
 * diagnostics as sent by the publishDiagnostics notification.
 */
export function WithLspDiagnosticsContext({children}: React.PropsWithChildren<{}>) {
    const [allDiags, _0] = useServerNotificationState(
        'textDocument/publishDiagnostics',
        new Map<DocumentUri, Diagnostic[]>(),
        async (params: PublishDiagnosticsParams) => diags =>
            new Map(diags).set(params.uri, params.diagnostics),
        []
    )

    return <LspDiagnosticsContext.Provider value={allDiags}>{children}</LspDiagnosticsContext.Provider>
}

/** Embeds a non-interactive diagnostic into the type `InteractiveDiagnostic`. */
export function lspDiagToInteractive(diag: Diagnostic): InteractiveDiagnostic {
    return { ...(diag as LeanDiagnostic), message: { text: diag.message } };
}
