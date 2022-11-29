

import * as monaco from 'monaco-editor/esm/vs/editor/editor.api.js'
import { LeanClient } from 'lean4web/client/src/editor/leanclient';
import * as React from 'react';
import { monacoSetup } from 'lean4web/client/src/monacoSetup';

monacoSetup()

const socketUrl = ((window.location.protocol === "https:") ? "wss://" : "ws://") + window.location.host + '/websocket/'

const uri = monaco.Uri.parse('file:///')
export const leanClient = new LeanClient(socketUrl, undefined, uri, () => {})

export const ConnectionContext = React.createContext(null);
