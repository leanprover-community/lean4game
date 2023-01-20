/* Partly copied from https://github.com/leanprover/vscode-lean4/blob/master/lean4-infoview/src/infoview/main.tsx */

import * as React from 'react';
import * as ReactDOM from 'react-dom/client';
import type { DidCloseTextDocumentParams, Location, DocumentUri } from 'vscode-languageserver-protocol';

import 'tachyons/css/tachyons.css';
// import '@vscode/codicons/dist/codicon.ttf';
import '@vscode/codicons/dist/codicon.css';
import '../../../../node_modules/lean4-infoview/src/infoview/index.css';

import { LeanFileProgressParams, LeanFileProgressProcessingInfo, defaultInfoviewConfig, EditorApi, InfoviewApi } from '@leanprover/infoview-api';

import { Infos } from '../../../../node_modules/lean4-infoview/src/infoview/infos';
import { AllMessages, WithLspDiagnosticsContext } from '../../../../node_modules/lean4-infoview/src/infoview/messages';
import { useClientNotificationEffect, useEventResult, useServerNotificationState } from '../../../../node_modules/lean4-infoview/src/infoview/util';
import { EditorContext, ConfigContext, ProgressContext, VersionContext } from '../../../../node_modules/lean4-infoview/src/infoview/contexts';
import { WithRpcSessions } from '../../../../node_modules/lean4-infoview/src/infoview/rpcSessions';
import { EditorConnection, EditorEvents } from '../../../../node_modules/lean4-infoview/src/infoview/editorConnection';
import { EventEmitter } from '../../../../node_modules/lean4-infoview/src/infoview/event';
import { ServerVersion } from '../../../../node_modules/lean4-infoview/src/infoview/serverVersion';


function Main(props: {}) {
    const ec = React.useContext(EditorContext);

    /* Set up updates to the global infoview state on editor events. */
    const config = useEventResult(ec.events.changedInfoviewConfig) ?? defaultInfoviewConfig;

    const [allProgress, _1] = useServerNotificationState(
        '$/lean/fileProgress',
        new Map<DocumentUri, LeanFileProgressProcessingInfo[]>(),
        async (params: LeanFileProgressParams) => (allProgress) => {
            const newProgress = new Map(allProgress);
            return newProgress.set(params.textDocument.uri, params.processing);
        },
        []
    );

    const curUri = useEventResult(ec.events.changedCursorLocation, loc => loc?.uri);

    useClientNotificationEffect(
        'textDocument/didClose',
        (params: DidCloseTextDocumentParams) => {
            if (ec.events.changedCursorLocation.current &&
                ec.events.changedCursorLocation.current.uri === params.textDocument.uri) {
                ec.events.changedCursorLocation.fire(undefined)
            }
        },
        []
    );

    const serverVersion =
        useEventResult(ec.events.serverRestarted, result => new ServerVersion(result.serverInfo?.version ?? ''))
    const serverStoppedResult = useEventResult(ec.events.serverStopped);
    // NB: the cursor may temporarily become `undefined` when a file is closed. In this case
    // it's important not to reconstruct the `WithBlah` wrappers below since they contain state
    // that we want to persist.
    let ret
    if (!serverVersion) {
        ret = <p>Waiting for Lean server to start...</p>
    } else if (serverStoppedResult){
        ret = <div><p>{serverStoppedResult.message}</p><p className="error">{serverStoppedResult.reason}</p></div>
    } else {
        ret = <div className="ma1">
            <Infos />
            {/* {curUri && <div className="mv2">
                <AllMessages uri={curUri} />
            </div>} */}
        </div>
    }

    return (
    <ConfigContext.Provider value={config}>
        <VersionContext.Provider value={serverVersion}>
            <WithRpcSessions>
                <WithLspDiagnosticsContext>
                    <ProgressContext.Provider value={allProgress}>
                        {ret}
                    </ProgressContext.Provider>
                </WithLspDiagnosticsContext>
            </WithRpcSessions>
        </VersionContext.Provider>
    </ConfigContext.Provider>
    );
}

/**
  * Render the Lean infoview into the DOM element `uiElement`.
  *
  * @param editorApi is a collection of methods which the infoview needs to be able to invoke
  * on the editor in order to function correctly (such as inserting text or moving the cursor).
  * @returns a collection of methods which must be invoked when the relevant editor events occur.
  */
export function renderInfoview(editorApi: EditorApi, uiElement: HTMLElement): InfoviewApi {
    const editorEvents: EditorEvents = {
        initialize: new EventEmitter(),
        gotServerNotification: new EventEmitter(),
        sentClientNotification: new EventEmitter(),
        serverRestarted: new EventEmitter(),
        serverStopped: new EventEmitter(),
        changedCursorLocation: new EventEmitter(),
        changedInfoviewConfig: new EventEmitter(),
        runTestScript: new EventEmitter(),
        requestedAction: new EventEmitter(),
    };

    // Challenge: write a type-correct fn from `Eventify<T>` to `T` without using `any`
    const infoviewApi: InfoviewApi = {
        initialize: async l => editorEvents.initialize.fire(l),
        gotServerNotification: async (method, params) => {
            editorEvents.gotServerNotification.fire([method, params]);
        },
        sentClientNotification: async (method, params) => {
            editorEvents.sentClientNotification.fire([method, params]);
        },
        serverRestarted: async r => editorEvents.serverRestarted.fire(r),
        serverStopped: async serverStoppedReason => {
            editorEvents.serverStopped.fire(serverStoppedReason)
        },
        changedCursorLocation: async loc => editorEvents.changedCursorLocation.fire(loc),
        changedInfoviewConfig: async conf => editorEvents.changedInfoviewConfig.fire(conf),
        requestedAction: async action => editorEvents.requestedAction.fire(action),
        // See https://rollupjs.org/guide/en/#avoiding-eval
        // eslint-disable-next-line @typescript-eslint/no-implied-eval
        runTestScript: async script => new Function(script)(),
        getInfoviewHtml: async () => document.body.innerHTML,
    };

    const ec = new EditorConnection(editorApi, editorEvents);

    editorEvents.initialize.on((loc: Location) => ec.events.changedCursorLocation.fire(loc))

    const root = ReactDOM.createRoot(uiElement)
    root.render(<React.StrictMode>
        <EditorContext.Provider value={ec}>
            <Main/>
        </EditorContext.Provider>
    </React.StrictMode>)

    return infoviewApi;
}
