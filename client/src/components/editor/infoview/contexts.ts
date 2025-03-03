import * as React from 'react'
import type { Diagnostic, DocumentUri } from 'vscode-languageserver-protocol'

import { defaultInfoviewConfig, InfoviewConfig, LeanFileProgressProcessingInfo } from '@leanprover/infoview-api'

import { EditorConnection } from './editorConnection'
import { ServerVersion } from './serverVersion'
import { DocumentPosition } from './util'

// Type-unsafe initializers for contexts which we immediately set up at the top-level.
// eslint-disable-next-line @typescript-eslint/no-unsafe-argument
export const EditorContext = React.createContext<EditorConnection>(null as any)
export const VersionContext = React.createContext<ServerVersion | undefined>(undefined)

export const ConfigContext = React.createContext<InfoviewConfig>(defaultInfoviewConfig)
export const LspDiagnosticsContext = React.createContext<Map<DocumentUri, Diagnostic[]>>(new Map())
export const ProgressContext = React.createContext<Map<DocumentUri, LeanFileProgressProcessingInfo[]>>(new Map())

/**
 * Certain infoview components and widget instances
 * utilize data that has been introduced above a specific position
 * in a Lean source file.
 *
 * For instance, if we declare a global constant with `def foo` on line 10,
 * we can immediately display it in a widget on line 11.
 * To achieve this, the widget code needs to have access
 * to the environment on line 11 as that environment contains `foo`.
 *
 * {@link EnvPosContext} stores the position in the file
 * from which an appropriate environment can be retrieved.
 * This is used to look up global constants,
 * in particular RPC methods (`@[server_rpc_method]`)
 * and widget modules (`@[widget_module]`).
 *
 * Note that {@link EnvPosContext} may, but need not,
 * be equal to any of the positions which the infoview keeps track of
 * (such as the editor cursor position).
 *
 * #### Infoview implementation details
 *
 * In the infoview, {@link EnvPosContext} is set as follows:
 * - in an `<InfoDisplay>`,
 *   it is the position at which the info block is being displayed:
 *   either a recent editor cursor position
 *   (when shown in the at-cursor `<InfoDisplay>`,
 *   this will lag behind the current editor cursor position
 *   while the `<InfoDisplay>` is in the process of updating),
 *   or a pinned position.
 * - in an `<InteractiveMessage>` that comes from a diagnostic
 *   emitted with a syntactic range,
 *   it is the start of the diagnostic's `fullRange`.
 */
export const EnvPosContext = React.createContext<DocumentPosition | undefined>(undefined)
