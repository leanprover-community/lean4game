import { VSCodeButton } from '@vscode/webview-ui-toolkit/react'
import * as React from 'react'
import * as ReactDOM from 'react-dom/client'
import type { DidCloseTextDocumentParams, DocumentUri, Location } from 'vscode-languageserver-protocol'

import '@vscode/codicons/dist/codicon.css'
import '@vscode/codicons/dist/codicon.ttf'
import 'tachyons/css/tachyons.css'
import './index.css'

import {
    defaultInfoviewConfig,
    EditorApi,
    InfoviewApi,
    LeanFileProgressParams,
    LeanFileProgressProcessingInfo,
} from '@leanprover/infoview-api'

import { ConfigContext, EditorContext, ProgressContext, VersionContext } from './infoview/contexts'
import { EditorConnection, EditorEvents } from './infoview/editorConnection'
import { EventEmitter } from './infoview/event'
import { Infos } from './infoview/infos'
import { AllMessages, WithLspDiagnosticsContext } from './infoview/messages'
import { WithRpcSessions } from './infoview/rpcSessions'
import { ServerVersion } from './infoview/serverVersion'
import { useClientNotificationEffect, useEventResult, useServerNotificationState } from './infoview/util'

import { useTranslation } from 'react-i18next'
import { Main } from './infoview/main'

/** The input field */
export function GameInfoview({editorApi}: {editorApi: EditorApi}) {
  let { t } = useTranslation()

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
    goToDefinition: new EventEmitter(),
  }

  // Challenge: write a type-correct fn from `Eventify<T>` to `T` without using `any`
  const infoviewApi: InfoviewApi = {
    initialize: async l => editorEvents.initialize.fire(l),
    gotServerNotification: async (method, params) => {
        editorEvents.gotServerNotification.fire([method, params])
    },
    sentClientNotification: async (method, params) => {
        editorEvents.sentClientNotification.fire([method, params])
    },
    serverRestarted: async r => editorEvents.serverRestarted.fire(r),
    serverStopped: async serverStoppedReason => {
        editorEvents.serverStopped.fire(serverStoppedReason)
    },
    changedCursorLocation: async loc => editorEvents.changedCursorLocation.fire(loc),
    changedInfoviewConfig: async conf => editorEvents.changedInfoviewConfig.fire(conf),
    requestedAction: async action => editorEvents.requestedAction.fire(action, action.kind),
    goToDefinition: async id => editorEvents.goToDefinition.fire(id, id),
    // See https://rollupjs.org/guide/en/#avoiding-eval
    // eslint-disable-next-line @typescript-eslint/no-implied-eval
    runTestScript: async script => new Function(script)(),
    getInfoviewHtml: async () => document.body.innerHTML,
  }
  const ec = new EditorConnection(editorApi, editorEvents)

  editorEvents.initialize.on((loc: Location) => ec.events.changedCursorLocation.fire(loc))

  return <EditorContext.Provider value={ec}>
        <Main />
    </EditorContext.Provider>
}
