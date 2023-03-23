/* Partly copied from https://github.com/leanprover/vscode-lean4/blob/master/lean4-infoview/src/infoview/main.tsx */

import * as React from 'react';
import type { DidCloseTextDocumentParams, DidChangeTextDocumentParams, Location, DocumentUri } from 'vscode-languageserver-protocol';

import 'tachyons/css/tachyons.css';
// import '@vscode/codicons/dist/codicon.ttf';
import '@vscode/codicons/dist/codicon.css';
import '../../../../node_modules/lean4-infoview/src/infoview/index.css';
import './infoview.css'

import { LeanFileProgressParams, LeanFileProgressProcessingInfo, defaultInfoviewConfig, EditorApi, InfoviewApi } from '@leanprover/infoview-api';

import { Infos } from './infos';
import { AllMessages, WithLspDiagnosticsContext } from './messages';
import { useClientNotificationEffect, useServerNotificationEffect, useEventResult, useServerNotificationState } from '../../../../node_modules/lean4-infoview/src/infoview/util';
import { EditorContext, ConfigContext, ProgressContext, VersionContext } from '../../../../node_modules/lean4-infoview/src/infoview/contexts';
import { WithRpcSessions } from '../../../../node_modules/lean4-infoview/src/infoview/rpcSessions';
import { ServerVersion } from '../../../../node_modules/lean4-infoview/src/infoview/serverVersion';
import { useAppDispatch, useAppSelector } from '../../hooks';
import { levelCompleted, selectCompleted } from '../../state/progress';
import { GameIdContext } from '../../App';


export function Main(props: {world: string, level: number}) {
    const ec = React.useContext(EditorContext);
    const gameId = React.useContext(GameIdContext)

    const dispatch = useAppDispatch()

    // Mark level as completed when server gives notification
    useServerNotificationEffect(
        '$/game/completed',
        (params: any) => {

            if (ec.events.changedCursorLocation.current &&
                ec.events.changedCursorLocation.current.uri === params.uri) {
                dispatch(levelCompleted({game: gameId, world: props.world, level: props.level}))
            }
        },
        []
    );

    const completed = useAppSelector(selectCompleted(gameId, props.world, props.level))

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
        ret = <div className="infoview vscode-light">
            {completed && <div className="level-completed">Level completed! 🎉</div>}
            <Infos />
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
