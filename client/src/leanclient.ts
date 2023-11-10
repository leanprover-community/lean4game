/* This file is based on `vscode-lean4/src/leanclient.ts` */

import {
  TextDocument, EventEmitter, Diagnostic,
  DocumentHighlight, Range, DocumentHighlightKind, workspace,
  Disposable, Uri, ConfigurationChangeEvent, OutputChannel, DiagnosticCollection,
  WorkspaceFolder, window
} from 'vscode'
import {
  DidChangeTextDocumentParams,
  DidCloseTextDocumentParams,
  DidOpenTextDocumentNotification,
  DocumentFilter,
  InitializeResult,
  MonacoLanguageClient as LanguageClient,
  LanguageClientOptions,
  PublishDiagnosticsParams,
  CloseAction, ErrorAction,
  RevealOutputChannelOn,
} from 'monaco-languageclient'
import { State } from 'vscode-languageclient'
import * as ls from 'vscode-languageserver-protocol'
import { toSocket } from 'vscode-ws-jsonrpc'

import {
  // toolchainPath, lakePath, addServerEnvPaths, serverArgs, serverLoggingEnabled, serverLoggingPath, shouldAutofocusOutput,
  getElaborationDelay
  // lakeEnabled
} from 'lean4web/client/src/editor/config'
// import { assert } from './utils/assert'
import { LeanFileProgressParams, LeanFileProgressProcessingInfo } from '@leanprover/infoview-api'
// import { LocalStorageService } from './utils/localStorage'
// import { batchExecute } from './utils/batch'
// import { readLeanVersion } from './utils/projectInfo'
import * as fs from 'fs'
import { URL } from 'url'
import { join } from 'path'
// import { logger } from './utils/logger'
import { SemVer } from 'semver'
// import { fileExists, isFileInFolder } from './utils/fsHelper'
import { c2pConverter, p2cConverter, patchConverters } from 'lean4web/client/src/editor/utils/converters'
import { WasmReader, WasmWriter, WebSocketMessageWriter, WebSocketMessageReader } from './wasm'

const escapeRegExp = (s: string) => s.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')

export type ServerProgress = Map<Uri, LeanFileProgressProcessingInfo[]>

export function getFullRange (diag: Diagnostic): Range {
  return (diag as any)?.fullRange || diag.range
}

export class LeanClient implements Disposable {
  running: boolean = false
  private client: LanguageClient | undefined
  // private toolchainPath: string
  // private readonly outputChannel: OutputChannel
  // private readonly storageManager: LocalStorageService
  private readonly workspaceFolder: WorkspaceFolder | undefined
  private readonly folderUri: Uri
  private readonly subscriptions: Disposable[] = []
  private noPrompt: boolean = false
  private showingRestartMessage: boolean = false
  // private readonly elanDefaultToolchain: string

  private readonly didChangeEmitter = new EventEmitter<DidChangeTextDocumentParams>()
  didChange = this.didChangeEmitter.event

  private readonly diagnosticsEmitter = new EventEmitter<PublishDiagnosticsParams>()
  diagnostics = this.diagnosticsEmitter.event

  private readonly didSetLanguageEmitter = new EventEmitter<string>()
  didSetLanguage = this.didSetLanguageEmitter.event

  private readonly didCloseEmitter = new EventEmitter<DidCloseTextDocumentParams>()
  didClose = this.didCloseEmitter.event

  private readonly customNotificationEmitter = new EventEmitter<{ method: string, params: any }>()
  /** Fires whenever a custom notification (i.e. one not defined in LSP) is received. */
  customNotification = this.customNotificationEmitter.event

  /** saved progress info in case infoview is opened, it needs to get all of it. */
  progress: ServerProgress = new Map()

  private readonly progressChangedEmitter = new EventEmitter<[string, LeanFileProgressProcessingInfo[]]>()
  progressChanged = this.progressChangedEmitter.event

  private readonly stoppedEmitter = new EventEmitter()
  stopped = this.stoppedEmitter.event

  private readonly restartedEmitter = new EventEmitter()
  restarted = this.restartedEmitter.event

  private readonly restartingEmitter = new EventEmitter()
  restarting = this.restartingEmitter.event

  private readonly restartedWorkerEmitter = new EventEmitter<string>()
  restartedWorker = this.restartedWorkerEmitter.event

  private readonly serverFailedEmitter = new EventEmitter<string>()
  serverFailed = this.serverFailedEmitter.event

  /** Files which are open. */
  private readonly isOpen: Map<string, TextDocument> = new Map()

  constructor (private readonly socketUrl: string, workspaceFolder: WorkspaceFolder | undefined, folderUri: Uri,
    public readonly showRestartMessage: () => void) {
    // this.storageManager = storageManager
    // this.outputChannel WebSocketMessageWriter= outputChannel
    this.workspaceFolder = workspaceFolder // can be null when opening adhoc files.
    this.folderUri = folderUri
    // this.elanDefaultToolchain = elanDefaultToolchain
    // this.subscriptions.push(workspace.onDidChangeConfiguration((e) => this.configChanged(e)))
  }

  dispose (): void {
    this.subscriptions.forEach((s) => s.dispose())
    if (this.isStarted()) void this.stop()
  }

  // async showRestartMessage (restartFile: boolean = false): Promise<void> {
  //   // if (!this.showingRestartMessage) {
  //   //   this.showingRestartMessage = true
  //   //   let restartItem: string
  //   //   let messageTitle: string
  //   //   if (!restartFile) {
  //   //     restartItem = 'Restart Lean Server'
  //   //     messageTitle = 'Lean Server has stopped unexpectedly.'
  //   //   } else {
  //   //     restartItem = 'Restart Lean Server on this file'
  //   //     messageTitle = 'The Lean Server has stopped processing this file.'
  //   //   }
  //   //   const item = await this.showErrorMessage(messageTitle, restartItem)
  //   //   this.showingRestartMessage = false
  //   //   if (item === restartItem) {
  //   //     void this.start()
  //   //     // if (restartFile && (window.activeTextEditor != null)) {
  //   //     //   await this.restartFile(window.activeTextEditor.document)
  //   //     // } else {
  //   //     //   void this.start()
  //   //     // }
  //   //   }
  //   // }
  // }

  async restart (): Promise<void> {
    const startTime = Date.now()

    console.log('[LeanClient] Restarting Lean Server')
    if (this.isStarted()) {
      await this.stop()
    }

    this.restartingEmitter.fire(undefined)
    // this.toolchainPath = this.storageManager.getLeanPath()
    // if (!this.toolchainPath) this.toolchainPath = toolchainPath()
    // let version = this.storageManager.getLeanVersion()
    // const env = addServerEnvPaths(process.env)
    // if (serverLoggingEnabled()) {
    //   env.LEAN_SERVER_LOG_DIR = serverLoggingPath()
    // }

    // let executable = lakePath() ||
    //       (this.toolchainPath ? join(this.toolchainPath, 'bin', 'lake') : 'lake')

    // check if the lake process will start (skip it on scheme: 'untitled' files)
    // let useLake = lakeEnabled() && this.folderUri && this.folderUri.scheme === 'file'
    // if (useLake) {
    //   let knownDate = false
    //   const lakefile = Uri.joinPath(this.folderUri, 'lakefile.lean')
    //   if (!await fileExists(new URL(lakefile.toString()))) {
    //     useLake = false
    //   } else {
    //     // see if we can avoid the more expensive checkLakeVersion call.
    //     const date = await this.checkToolchainVersion(this.folderUri)
    //     if (date != null) {
    //       // Feb 16 2022 is when the 3.1.0.pre was released.
    //       useLake = date >= new Date(2022, 1, 16)
    //       knownDate = true
    //     }
    //     if (useLake && !knownDate) {
    //       useLake = await this.checkLakeVersion(executable, version)
    //     }
    //   }
    // }

    // if (!useLake) {
    //   executable = (this.toolchainPath) ? join(this.toolchainPath, 'bin', 'lean') : 'lean'
    // }

    // const cwd = this.folderUri?.fsPath
    // if (!cwd && !version) {
    //   // Fixes issue #227, for adhoc files it would pick up the cwd from the open folder
    //   // which is not what we want.  For adhoc files we want the (default) toolchain instead.
    //   version = this.elanDefaultToolchain
    // }

    // let options = version ? ['+' + version] : []
    // if (useLake) {
    //   options = options.concat(['serve', '--'])
    // } else {
    //   options = options.concat(['--server'])
    // }

    // Add folder name to command-line so that it shows up in `ps aux`.
    // if (cwd) {
    //   options.push('' + cwd)
    // } else {
    //   options.push('untitled')
    // }

    // const serverOptions: ServerOptions = {
    //   command: executable,
    //   args: options.concat(serverArgs()),
    //   options: {
    //     cwd,
    //     env
    //   }
    // }

    const clientOptions: LanguageClientOptions = {
      // use a language id as a document selector
      documentSelector: ['lean4'],
      initializationOptions: {
        editDelay: getElaborationDelay(), hasWidgets: true
      },
      connectionOptions: {
        maxRestartCount: 0,
        cancellationStrategy: undefined as any
      },
      // disable the default error handler
      errorHandler: {
        error: () => ({ action: ErrorAction.Continue }),
        closed: () => ({ action: CloseAction.DoNotRestart })
      },
      middleware: {
        handleDiagnostics: (uri, diagnostics, next) => {
          next(uri, diagnostics)
          if (this.client == null) return
          const uri_ = c2pConverter.asUri(uri)
          const diagnostics_ = []
          for (const d of diagnostics) {
            const d_: ls.Diagnostic = {
              ...c2pConverter.asDiagnostic(d)
            }
            diagnostics_.push(d_)
          }
          this.diagnosticsEmitter.fire({ uri: uri_, diagnostics: diagnostics_ })
        },

        // didOpen: async () => {
        //   // Note: as per the LSP spec: An open notification must not be sent more than once
        //   // without a corresponding close notification send before. This means open and close
        //   // notification must be balanced and the max open count for a particular textDocument
        //   // is one.  So this even does nothing the notification is handled by the
        //   // openLean4Document method below after the 'lean4' languageId is established and
        //   // it has weeded out documents opened to invisible editors (like 'git:' schemes and
        //   // invisible editors created for Ctrl+Hover events.  A side effect of unbalanced
        //   // open/close notification is leaking 'lean --worker' processes.
        //   // See https://github.com/microsoft/vscode/issues/78453).

        // },

        didChange: async (data, next) => {
          await next(data)
          if (!this.running || (this.client == null)) return // there was a problem starting lean server.
          const params = c2pConverter.asChangeTextDocumentParams(data)
          this.didChangeEmitter.fire(params)
        },

        didClose: async (doc, next) => {
          if (!this.isOpen.delete(doc.uri.toString())) {
            return
          }
          await next(doc)
          if (!this.running || (this.client == null)) return // there was a problem starting lean server.
          const params = c2pConverter.asCloseTextDocumentParams(doc)
          this.didCloseEmitter.fire(params)
        },

        provideDocumentHighlights: async (doc, pos, ctok, next) => {
          const leanHighlights = await next(doc, pos, ctok)
          if (leanHighlights?.length) return leanHighlights

          // vscode doesn't fall back to textual highlights,
          // so we need to do that manually
          await new Promise((res) => setTimeout(res, 250))
          if (ctok.isCancellationRequested) return

          const wordRange = doc.getWordRangeAtPosition(pos)
          if (wordRange == null) return
          const word = doc.getText(wordRange)

          const highlights: DocumentHighlight[] = []
          const text = doc.getText()
          const nonWordPattern = '[`~@$%^&*()-=+\\[{\\]}⟨⟩⦃⦄⟦⟧⟮⟯‹›\\\\|;:\",./\\s]|^|$'
          const regexp = new RegExp(`(?<=${nonWordPattern})${escapeRegExp(word)}(?=${nonWordPattern})`, 'g')
          for (const match of text.matchAll(regexp)) {
            const start = doc.positionAt(match.index ?? 0)
            highlights.push({
              range: new Range(start, start.translate(0, match[0].length)),
              kind: DocumentHighlightKind.Text
            })
          }

          return highlights
        }
      }
    }
    if (!this.client) {
      this.client = new LanguageClient({
        id: 'lean4',
        name: 'Lean 4',
        clientOptions,
        connectionProvider: {
          get: async () => {
            return await new Promise((resolve, reject) => {
              const worker = new Worker("worker.js")
              const reader = new WasmReader(worker)
              const writer = new WasmWriter(worker)
              resolve({
                reader,
                writer
              })
            })
          }
        }
      })
    } else {
      await this.client.start()
    }


    // HACK: Prevent monaco from panicking when the Lean server crashes
    this.client.handleFailedRequest = (type, token: any, error: any, defaultValue, showNotification?: boolean) => {
      return defaultValue
    }

    let insideRestart = true
    patchConverters(this.client.protocol2CodeConverter, this.client.code2ProtocolConverter)
    try {
      this.client.onDidChangeState(async (s) => {
        // see https://github.com/microsoft/vscode-languageserver-node/issues/825
        if (s.newState === State.Starting) {
          console.log('[LeanClient] starting')
        } else if (s.newState === State.Running) {
          const end = Date.now()
          console.log(`[LeanClient] running, started in ${end - startTime} ms`)
          this.running = true // may have been auto restarted after it failed.
          if (!insideRestart) {
            this.restartedEmitter.fire(undefined)
          }
        } else if (s.newState === State.Stopped) {
          this.running = false
          console.log('[LeanClient] has stopped or it failed to start')
          if (!this.noPrompt) {
            // only raise this event and show the message if we are not the ones
            // who called the stop() method.
            this.stoppedEmitter.fire({ message: 'Lean server has stopped.', reason: '' })
            await this.showRestartMessage()
          }
        }
      })
      await this.client.start()
      // tell the new client about the documents that are already open!
      // for (const key of this.isOpen.keys()) {
      //   const doc = this.isOpen.get(key)
      //   if (doc != null) this.notifyDidOpen(doc)
      // }
      // if we got this far then the client is happy so we are running!
      this.running = true
    } catch (error) {
      console.log(error)
      this.serverFailedEmitter.fire('' + error)
      insideRestart = false
      return
    }

    // HACK(WN): Register a default notification handler to fire on custom notifications.
    // A mechanism to do this is provided in vscode-jsonrpc. One can register a `StarNotificationHandler`
    // here: https://github.com/microsoft/vscode-languageserver-node/blob/b2fc85d28a1a44c22896559ee5f4d3ba37a02ef5/jsonrpc/src/common/connection.ts#L497
    // which fires on any LSP notifications not in the standard, for example the `$/lean/..` ones.
    // However this mechanism is not exposed in vscode-languageclient, so we hack around its implementation.
    const starHandler = (method: string, params_: any) => {
      if (method === '$/lean/fileProgress' && (this.client != null)) {
        const params = params_ as LeanFileProgressParams
        const uri = p2cConverter.asUri(params.textDocument.uri)
        this.progressChangedEmitter.fire([uri.toString(), params.processing])
        // save the latest progress on this Uri in case infoview needs it later.
        this.progress.set(uri, params.processing)
      }

      this.customNotificationEmitter.fire({ method, params: params_ })
    }
    // eslint-disable-next-line @typescript-eslint/no-unsafe-argument
    this.client.onNotification(starHandler as any, () => {})

    // Reveal the standard error output channel when the server prints something to stderr.
    // The vscode-languageclient library already takes care of writing it to the output channel.
    // let stderrMsgBoxVisible = false;
    // (this.client)._serverProcess.stderr.on('data', async (chunk: Buffer) => {
    //   if (shouldAutofocusOutput()) {
    //     this.client?.outputChannel.show(true)
    //   } else if (!stderrMsgBoxVisible) {
    //     stderrMsgBoxVisible = true
    //     const outputItem = 'Show stderr output'
    //     const outPrompt = `Lean server printed an error:\n${chunk.toString()}`
    //     if (await window.showErrorMessage(outPrompt, outputItem) === outputItem) {
    //       this.outputChannel.show(false)
    //     }
    //     stderrMsgBoxVisible = false
    //   }
    // })

    this.restartedEmitter.fire(undefined)
    insideRestart = false
  }

  async openLean4Document (doc: TextDocument) {
    if (this.isOpen.has(doc.uri.toString())) return
    if (!await this.isSameWorkspace(doc.uri)) {
      // skip it, this file belongs to a different workspace...
      return
    }

    this.isOpen.set(doc.uri.toString(), doc)

    if (!this.running) return // there was a problem starting lean server.

    // didOpenEditor may have also changed the language, so we fire the
    // event here because the InfoView should be wired up to receive it now.
    this.didSetLanguageEmitter.fire(doc.languageId)

    this.notifyDidOpen(doc)
  }

  notifyDidOpen (doc: TextDocument) {
    // BUG: was `DidOpenTextDocumentNotification.type` instead of the string, but that failed
    void this.client?.sendNotification('textDocument/didOpen', {
      textDocument: {
        uri: doc.uri.toString(),
        languageId: doc.languageId,
        version: 1,
        text: doc.getText()
      }
    })
  }

  async isSameWorkspace (uri: Uri): Promise<boolean> {
    // if (this.folderUri) {
    //   if (this.folderUri.scheme !== uri.scheme) return false
    //   if (this.folderUri.scheme === 'file') {
    //     const realPath1 = await fs.promises.realpath(this.folderUri.fsPath)
    //     const realPath2 = await fs.promises.realpath(uri.fsPath)
    //     return isFileInFolder(realPath2, realPath1)
    //   } else {
    //     return uri.toString().startsWith(this.folderUri.toString())
    //   }
    // } else {
    //   return uri.scheme === 'untitled'
    // }
    return false
  }

  getWorkspaceFolder (): string {
    return this.folderUri?.toString()
  }

  async start (): Promise<void> {
    return await this.restart()
  }

  isStarted (): boolean {
    return this.client !== undefined
  }

  isRunning (): boolean {
    if (this.client != null) {
      return this.running
    }
    return false
  }

  async stop (): Promise<void> {
    // assert(() => this.isStarted())
    if ((this.client != null) && this.running) {
      this.noPrompt = true
      try {
        // some timing conditions can happen while running unit tests that cause
        // this to throw an exception which then causes those tests to fail.
        await this.client.stop()
      } catch (e) {
        console.log(`[LeanClient] Error stopping language client: ${e}`)
      }
    }

    this.noPrompt = false
    this.progress = new Map()
    this.client = undefined
    this.running = false
  }

  configChanged (e: ConfigurationChangeEvent): void {
    // let newToolchainPath = this.storageManager.getLeanPath()
    // if (!newToolchainPath) newToolchainPath = toolchainPath()
    // if (this.toolchainPath !== newToolchainPath) {
    //  void this.restart()
    // }
  }

  async restartFile (doc: TextDocument): Promise<void> {
    if (!this.running) return // there was a problem starting lean server.

    // assert(() => this.isStarted())

    if (!await this.isSameWorkspace(doc.uri)) {
      // skip it, this file belongs to a different workspace...
      return
    }
    const uri = doc.uri.toString()
    console.log(`[LeanClient] Restarting File: ${uri}`)
    // This causes a text document version number discontinuity. In
    // (didChange (oldVersion) => restartFile => didChange (newVersion))
    // the client emits newVersion = oldVersion + 1, despite the fact that the
    // didOpen packet emitted below initializes the version number to be 1.
    // This is not a problem though, since both client and server are fine
    // as long as the version numbers are monotonous.
    void this.client?.sendNotification('textDocument/didClose', {
      textDocument: {
        uri
      }
    })
    void this.client?.sendNotification('textDocument/didOpen', {
      textDocument: {
        uri,
        languageId: 'lean4',
        version: 1,
        text: doc.getText()
      }
    })
    this.restartedWorkerEmitter.fire(uri)
  }

  // eslint-disable-next-line @typescript-eslint/explicit-module-boundary-types
  async sendRequest (method: string, params: any): Promise<any> {
    return this.running && (this.client != null)
      ? await this.client.sendRequest(method, params)
      : await new Promise<any>((_, reject) => { reject('Client is not running') })
  }

  // eslint-disable-next-line @typescript-eslint/explicit-module-boundary-types
  sendNotification (method: string, params: any): Promise<void> | undefined {
    return this.running && (this.client != null) ? this.client.sendNotification(method, params) : undefined
  }

  async getDiagnosticParams (uri: Uri, diagnostics: readonly Diagnostic[]): Promise<PublishDiagnosticsParams> {
    const params: PublishDiagnosticsParams = {
      uri: c2pConverter.asUri(uri),
      diagnostics: await c2pConverter.asDiagnostics(diagnostics as Diagnostic[])
    }
    return params
  }

  getDiagnostics (): DiagnosticCollection | undefined {
    return this.running ? this.client?.diagnostics : undefined
  }

  get initializeResult (): InitializeResult | undefined {
    return this.running ? this.client?.initializeResult : undefined
  }

  private async checkToolchainVersion (folderUri: Uri): Promise<Date | undefined> {
    // see if we have a well known toolchain label that corresponds
    // to a known date like 'leanprover/lean4:nightly-2022-02-01'
    // const toolchainVersion = await readLeanVersion(folderUri)
    // if (toolchainVersion) {
    //   const match = /^leanprover\/lean4:nightly-(\d+)-(\d+)-(\d+)$/.exec(toolchainVersion)
    //   if (match != null) {
    //     return new Date(parseInt(match[1]), parseInt(match[2]) - 1, parseInt(match[3]))
    //   }
    //   if (toolchainVersion === 'leanprover/lean4:stable') {
    //     return new Date(2022, 2, 1)
    //   }
    // }
    return undefined
  }

  // async checkLakeVersion (executable: string, version: string): Promise<boolean> {
  //   // Check that the Lake version is high enough to support "lake serve" option.
  //   const versionOptions = version ? ['+' + version, '--version'] : ['--version']
  //   const start = Date.now()
  //   const lakeVersion = await batchExecute(executable, versionOptions, this.folderUri?.fsPath, undefined)
  //   logger.log(`[LeanClient] Ran '${executable} ${versionOptions.join(' ')}' in ${Date.now() - start} ms`)
  //   const actual = this.extractVersion(lakeVersion)
  //   if (actual.compare('3.0.0') > 0) {
  //     return true
  //   }
  //   return false
  // }

  // private extractVersion (v: string | undefined): SemVer {
  //   if (!v) return new SemVer('0.0.0')
  //   const prefix = 'Lake version'
  //   if (v.startsWith(prefix)) v = v.slice(prefix.length).trim()
  //   const pos = v.indexOf('(')
  //   if (pos > 0) v = v.slice(0, pos).trim()
  //   try {
  //     return new SemVer(v)
  //   } catch {
  //     return new SemVer('0.0.0')
  //   }
  // }
}
