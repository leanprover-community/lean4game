import * as React from 'react'
import { useEffect, useState, useRef } from 'react'
import Split from 'react-split'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faHome, faArrowRight } from '@fortawesome/free-solid-svg-icons'
import { CircularProgress } from '@mui/material'
import type { Location } from 'vscode-languageserver-protocol'
import { LeanMonaco, LeanMonacoEditor, LeanMonacoOptions } from 'lean4monaco'
import { setupMonacoClient } from 'lean4monaco/dist/monacoleanclient'
import type { EditorApi, InfoviewApi } from '@leanprover/infoview-api'
import { EditorContext } from '../../../node_modules/vscode-lean4/lean4-infoview/src/infoview/contexts'
import { EditorConnection, EditorEvents } from '../../../node_modules/vscode-lean4/lean4-infoview/src/infoview/editorConnection'
import { EventEmitter } from '../../../node_modules/vscode-lean4/lean4-infoview/src/infoview/event'
import { Button } from './button'
import { Markdown } from './markdown'
import { MonacoEditorContext } from './infoview/context'
import { DualEditor } from './infoview/main'
import { DeletedHints, Hint, Hints, MoreHelpButton, filterHints } from './hints'
import path from 'path';

import '@fontsource/roboto/300.css'
import '@fontsource/roboto/400.css'
import '@fontsource/roboto/500.css'
import '@fontsource/roboto/700.css'
import '../css/level.css'
import { LevelAppBar } from './app_bar'
import { isLastStepWithErrors, lastStepHasErrors } from './infoview/goals'
import { useTranslation } from 'react-i18next'
import i18next from 'i18next'
import { useGameTranslation } from '../utils/translation'
import { InventoryPanel } from './inventory/inventory_panel'
import { useAtom } from 'jotai'
import { codeAtom, leanMonacoAtom, lockEditorModeAtom, proofAtom, selectionsAtom, typewriterModeAtom } from '../store/editor-atoms'
import { gameIdAtom, levelIdAtom, worldIdAtom } from '../store/location-atoms'
import { gameInfoAtom, levelInfoAtom } from '../store/query-atoms'
import { deletedChatAtom, helpAtom, selectedStepAtom } from '../store/chat-atoms'
import { inventoryOverviewAtom } from '../store/inventory-atoms'
import { mobileAtom } from '../store/preferences-atoms'

const reconfigureLeanMonacoClient = async (leanMonaco: LeanMonaco, options: LeanMonacoOptions) => {
  const maybeLeanMonaco = leanMonaco as unknown as {
    clientProvider?: {
      getClients?: () => Array<{ getClientFolder?: () => unknown; stop?: () => Promise<void> }>
      stopClient?: (folder: unknown) => Promise<void>
      setupClient?: unknown
    }
    getWebSocketOptions?: (options: LeanMonacoOptions) => unknown
  }
  if (!maybeLeanMonaco.clientProvider || !maybeLeanMonaco.getWebSocketOptions) {
    return
  }
  maybeLeanMonaco.clientProvider.setupClient = setupMonacoClient(
    maybeLeanMonaco.getWebSocketOptions(options) as any
  )
  const clients = maybeLeanMonaco.clientProvider.getClients?.() ?? []
  for (const client of clients) {
    const folder = client?.getClientFolder?.()
    if (folder && maybeLeanMonaco.clientProvider.stopClient) {
      await maybeLeanMonaco.clientProvider.stopClient(folder)
    } else {
      await client?.stop?.()
    }
  }
}

function Level() {
  const { t: gT, i18n } = useGameTranslation()
  const [gameId] = useAtom(gameIdAtom)
  const [worldId] = useAtom(worldIdAtom)
  const [levelId] = useAtom(levelIdAtom)
  const [{ data: gameInfo }] = useAtom(gameInfoAtom)

  // Load the namespace of the game
  i18n.loadNamespaces(gameId ?? "").catch(err => {
    console.warn(`translations for ${gameId} do not exist.`)
  })

  // set the window title
  useEffect(() => {
    if (gameInfo?.title) {
      window.document.title = gT(gameInfo.title)
    }
  }, [gameInfo?.title, i18n.language])


  if (levelId == 0) return <Introduction />
  return <PlayableLevel key={`${worldId}/${levelId}`} />
}

function ChatPanel({lastLevel, visible = true}: {lastLevel: boolean, visible: boolean}) {
  let { t } = useTranslation()
  const { t : gT } = useGameTranslation()
  const chatRef = useRef<HTMLDivElement>(null)
  const [mobile] = useAtom(mobileAtom)
  const [gameId, navigateToGame] = useAtom(gameIdAtom)
  const [levelId, navigateToLevel] = useAtom(levelIdAtom)
  const [{ data: levelInfo }] = useAtom(levelInfoAtom)
  const [help] = useAtom(helpAtom)
  const [proof] = useAtom(proofAtom)
  const [deletedChat] = useAtom(deletedChatAtom)
  const [selectedStep, setSelectedStep] = useAtom(selectedStepAtom)

  let k = proof?.steps.length ? proof?.steps.length - (lastStepHasErrors(proof) ? 2 : 1) : 0

  function toggleSelection(line: number) {
    return (ev: any) => {
      console.debug('toggled selection')
      if (selectedStep == line) {
        setSelectedStep(undefined)
      } else {
        setSelectedStep(line)
      }
    }
  }

  useEffect(() => {
    // TODO: For some reason this is always called twice
    console.debug('scroll chat')
    if (!mobile) {
      chatRef.current!.lastElementChild?.scrollIntoView() //scrollTo(0,0)
    }
  }, [proof, help])

  // Scroll to element if selection changes
  useEffect(() => {
    if (typeof selectedStep !== 'undefined') {
      Array.from(chatRef.current!.getElementsByClassName(`step-${selectedStep}`)).map((elem) => {
        elem.scrollIntoView({block: "center"})
      })
    }
  }, [selectedStep])

  // useEffect(() => {
  //   // // Scroll to top when loading a new level
  //   // // TODO: Thats the wrong behaviour probably
  //   // chatRef.current!.scrollTo(0,0)
  // }, [gameId, worldId, levelId])

  let introText: Array<string> = gT(levelInfo?.introduction ?? "").split(/\n(\s*\n)+/)

  const focusRef = useRef<HTMLButtonElement>()
  useEffect(() => {
   if (proof?.completed) {
     focusRef.current?.focus()
   }
  }, [!!proof?.completed])

  return <div className={`chat-panel ${visible ? '' : 'hidden'}`}>
    <div ref={chatRef} className="chat">
      {introText?.filter(it => it.trim()).map(((it, i) =>
        // Show the level's intro text as hints, too
        <Hint key={`intro-p-${i}`}
          hint={{text: it, hidden: false, rawText: it, varNames: []}} step={0} selected={selectedStep} toggleSelection={toggleSelection(0)} />
      ))}
      {proof?.steps.map((step, i) => {
        let filteredHints = filterHints(step.goals[0]?.hints, proof?.steps[i-1]?.goals[0]?.hints)
        if (step.goals.length > 0 && !isLastStepWithErrors(proof, i)) {
          return <Hints key={`hints-${i}`}
          hints={filteredHints} showHidden={help.has(i)} step={i}
          selected={selectedStep} toggleSelection={toggleSelection(i)} lastLevel={i == proof?.steps.length - 1}/>
        }
      })}

      {/* {modifiedHints.map((step, i) => {
        // It the last step has errors, it will have the same hints
        // as the second-to-last step. Therefore we should not display them.
        if (!(i == proof?.steps.length - 1 && withErr)) {
          // TODO: Should not use index as key.
          return <Hints key={`hints-${i}`}
            hints={step} showHidden={showHelp?.has(i)} step={i}
            selected={selectedStep} toggleSelection={toggleSelection(i)} lastLevel={i == proof?.steps.length - 1}/>
        }
      })} */}
      <DeletedHints hints={deletedChat}/>
      {proof?.completed &&
        <>
          <div className={`message information recent step-${k}${selectedStep == k ? ' selected' : ''}`} onClick={toggleSelection(k)}>
            {t("Level completed! 🎉")}
          </div>
          {levelInfo?.conclusion?.trim() &&
            <div className={`message information recent step-${k}${selectedStep == k ? ' selected' : ''}`} onClick={toggleSelection(k)}>
              <Markdown>{gT(levelInfo?.conclusion ?? "")}</Markdown>
            </div>
          }
        </>
      }
    </div>
    <div className="button-row">
      {proof?.completed && (lastLevel ?
        <Button ref={focusRef} onClick={() => {if (gameId) navigateToGame(gameId)}} >
          <FontAwesomeIcon icon={faHome} />&nbsp;{t("Home")}
        </Button> :
        <Button ref={focusRef} onClick={() => {if(levelId !== undefined) navigateToLevel(levelId + 1)}}  >
          {t("Next")}&nbsp;<FontAwesomeIcon icon={faArrowRight} />
        </Button>)
        }
      <MoreHelpButton selected={null} />
    </div>
  </div>
}


function ExercisePanel({codeviewRef, infoviewRef, visible=true}: {codeviewRef: React.MutableRefObject<HTMLDivElement>, infoviewRef: React.MutableRefObject<HTMLDivElement>, visible?: boolean}) {
  return <div className={`exercise-panel ${visible ? '' : 'hidden'}`}>
    <div ref={infoviewRef} className="infoview" style={{display: 'none'}}></div>
    <div className="exercise">
      <DualEditor codeviewRef={codeviewRef} />
    </div>
  </div>
}

function PlayableLevel() {
  let { t } = useTranslation()
  const { t : gT } = useGameTranslation()
  const codeviewRef = useRef<HTMLDivElement>(null)
  const infoviewRef = useRef<HTMLDivElement>(null)
  const [leanMonaco] = useAtom(leanMonacoAtom)
  const [gameId] = useAtom(gameIdAtom)
  const [worldId] = useAtom(worldIdAtom)
  const [levelId] = useAtom(levelIdAtom)
  const [typewriterMode, setTypewriterMode] = useAtom(typewriterModeAtom)
  const [mobile] = useAtom(mobileAtom)
  const [code] = useAtom(codeAtom)
  const [{ data: gameInfo }] = useAtom(gameInfoAtom)
  const [{ data: levelInfo, isLoading: levelInfoIsLoading }] = useAtom(levelInfoAtom)
  // Only for mobile layout
  const [pageNumber, setPageNumber] = useState(0)
  // set to true to prevent switching between typewriter and editor
  const [lockEditorMode] = useAtom(lockEditorModeAtom)
  const [, setTypewriterInput] = useState("")
  const lastLevel = worldId && (levelId !== undefined) && levelId >= (gameInfo?.worldSize?.[worldId] ?? 0)

  // When clicking on an inventory item, the inventory is overlayed by the item's doc.
  // If this state is set to a pair `(name, type)` then the according doc will be open.
  // Set `inventoryDoc` to `null` to close the doc
  const [inventoryDoc, setInventoryDoc] = useState<{name: string, type: string} | null>(null)
  function closeInventoryDoc () {setInventoryDoc(null)}

  const [leanMonacoEditor, setLeanMonacoEditor] = useState<LeanMonacoEditor|null>(null)
  const [editorConnection, setEditorConnection] = useState<null|EditorConnection>(null)

  // Start the editor
  useEffect(() => {
    if (leanMonaco) {
      const leanMonacoEditor = new LeanMonacoEditor()
      const uriStr = `file:///${worldId}/${levelId}.lean`

      ;(async () => {
        await leanMonaco!.whenReady
        console.debug('[demo]: starting editor')
        await leanMonacoEditor.start(codeviewRef.current!, uriStr, code ?? "")
        console.debug('[demo]: editor started')
        setLeanMonacoEditor(leanMonacoEditor)

        // TODO: old stuff from here on

        const infoProvider = leanMonaco.infoProvider as {
        editorApi: EditorApi
        webviewPanel?: { api: InfoviewApi, visible: boolean }
        sendConfig?: () => Promise<void>
        sendPosition?: () => Promise<void>
      } | undefined

      if (!infoProvider?.editorApi) {
        console.warn('Lean infoview is not ready yet.')
        return
      }

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
      }

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
        requestedAction: async action => editorEvents.requestedAction.fire(action),
        runTestScript: async script => new Function(script)(),
        getInfoviewHtml: async () => document.body.innerHTML,
      }

      infoProvider.webviewPanel = {
        api: infoviewApi,
        visible: true,
      }

      const editorConnection = new EditorConnection(infoProvider.editorApi, editorEvents)
      setEditorConnection(editorConnection)

      const model = leanMonacoEditor.editor?.getModel()
      const fireCursorLocation = () => {
        const selection = leanMonacoEditor.editor.getSelection()
        const position = leanMonacoEditor.editor.getPosition()
        if (!selection || !model) {
          if (!position || !model) {
            return
          }
          const loc: Location = {
            uri: model.uri.toString(),
            range: {
              start: {
                line: position.lineNumber - 1,
                character: position.column - 1,
              },
              end: {
                line: position.lineNumber - 1,
                character: position.column - 1,
              },
            },
          }
          editorEvents.changedCursorLocation.fire(loc)
          return
        }
        const loc: Location = {
          uri: model.uri.toString(),
          range: {
            start: {
              line: selection.startLineNumber - 1,
              character: selection.startColumn - 1,
            },
            end: {
              line: selection.endLineNumber - 1,
              character: selection.endColumn - 1,
            },
          },
        }
        editorEvents.changedCursorLocation.fire(loc)
      }

      fireCursorLocation()
      leanMonacoEditor.editor.onDidChangeCursorSelection(() => {
        fireCursorLocation()
      })

      await infoProvider.sendConfig?.()
      await infoProvider.sendPosition?.()

      })()

      return () => {
        leanMonacoEditor.dispose()
      }
    }
  }, [leanMonaco, worldId, levelId])

  // /** Unused. Was implementing an undo button, which has been replaced by `deleteProof` inside
  //  * `TypewriterInterface`.
  //  */
  // const handleUndo = () => {
  //   const endPos = leanMonacoEditor?.editor.getModel().getFullModelRange().getEndPosition()
  //   let range
  //   console.log(endPos?.column)
  //   if (endPos?.column === 1) {
  //     range = monaco.Selection.fromPositions(
  //       new monaco.Position(endPos.lineNumber - 1, 1),
  //       endPos
  //     )
  //   } else {
  //     range = monaco.Selection.fromPositions(
  //       new monaco.Position(endPos.lineNumber, 1),
  //       endPos
  //     )
  //   }
  //   leanMonacoEditor?.editor.executeEdits("undo-button", [{
  //     range,
  //     text: "",
  //     forceMoveMarkers: false
  //   }]);
  // }

  // Select and highlight proof steps and corresponding hints
  // TODO: with the new design, there is no difference between the introduction and
  // a hint at the beginning of the proof...
  const [selectedStep, setSelectedStep] = useState<number>()


  useEffect (() => {
    // Lock editor mode
    if (levelInfo?.template) {
      const model = leanMonacoEditor?.editor?.getModel()

      if (model) {
        let code = model.getLinesContent()

        // console.log(`insert. code: ${code}`)
        // console.log(`insert. join: ${code.join('')}`)
        // console.log(`insert. trim: ${code.join('').trim()}`)
        // console.log(`insert. length: ${code.join('').trim().length}`)
        // console.log(`insert. range: ${editor.getModel().getFullModelRange()}`)


        // TODO: It does seem that the template is always indented by spaces.
        // This is a hack, assuming there are exactly two.
        if (!code.join("").trim().length) {
          console.debug(`inserting template:\n${levelInfo?.template}`)
          // TODO: This does not work! HERE
          // Probably overwritten by a query to the server
          leanMonacoEditor?.editor.executeEdits("template-writer", [{
            range: model.getFullModelRange(),
            text: levelInfo?.template + `\n`,
            forceMoveMarkers: true
          }])
        } else {
          console.debug(`not inserting template.`)
        }
      }
    } else {
    }
  }, [levelInfo, levelId, worldId, gameId, leanMonacoEditor?.editor])


  useEffect(() => {
    // TODO: That's a problem if the saved proof contains an error
    // Reset command line input when loading a new level
    setTypewriterInput("")

  }, [gameId, worldId, levelId])

  useEffect(() => {
    const model = leanMonacoEditor?.editor?.getModel()
    if (!(typewriterMode) && model) {
      // Delete last input attempt from command line
      leanMonacoEditor?.editor.executeEdits("typewriter", [{
        range: model.getFullModelRange(),
        text: "",
        forceMoveMarkers: false
      }]);
      leanMonacoEditor?.editor.focus()
    }
  }, [typewriterMode])

  // useEffect(() => {
  //   // Forget whether hidden hints are displayed for steps that don't exist yet
  //   if (proof?.steps.length) {
  //     console.debug(Array.from(help))
  //     setHelp([...new Set(Array.from(help).filter(i => (i < proof?.steps.length)))])
  //   }
  // }, [proof])

  // // save showed help in store
  // useEffect(() => {
  //   if (proof?.steps.length) {
  //     console.debug(`showHelp:\n ${showHelp}`)
  //     setHelp(Array.from(showHelp))
  //   }
  // }, [showHelp])

  // Effect when command line mode gets enabled
  useEffect(() => {
    const model = leanMonacoEditor?.editor?.getModel()
    if (model&& (typewriterMode)) {
      let code = model.getLinesContent().filter(line => line.trim())
      leanMonacoEditor?.editor.executeEdits("typewriter", [{
        range: model.getFullModelRange(),
        text: code.length ? code.join('\n') + '\n' : '',
        forceMoveMarkers: true
      }]);

      // let endPos = editor.getModel().getFullModelRange().getEndPosition()
      // if (editor.getModel().getLineContent(endPos.lineNumber).trim() !== "") {
      //   editor.executeEdits("typewriter", [{
      //     range: monaco.Selection.fromPositions(endPos, endPos),
      //     text: "\n",
      //     forceMoveMarkers: true
      //   }]);
      // }
      // let endPos = editor.getModel().getFullModelRange().getEndPosition()
      // let currPos = editor.getPosition()
      // if (currPos.column != 1 || (currPos.lineNumber != endPos.lineNumber && currPos.lineNumber != endPos.lineNumber - 1)) {
      //   // This is not a position that would naturally occur from Typewriter, reset:
      //   editor.setSelection(monaco.Selection.fromPositions(endPos, endPos))
      // }
    }
  }, [leanMonacoEditor, leanMonacoEditor?.editor, typewriterMode, lockEditorMode])

  return <>
    <div style={levelInfoIsLoading? undefined : {display: "none"}} className="app-content loading"><CircularProgress /></div>
            <EditorContext.Provider value={editorConnection}>
              <MonacoEditorContext.Provider value={leanMonacoEditor?.editor}>
                <LevelAppBar
                  pageNumber={pageNumber} setPageNumber={setPageNumber}
                  isLoading={levelInfoIsLoading}
                  levelTitle={(mobile ? "" : t("Level")) + ` ${levelId} / ${worldId ? gameInfo?.worldSize?.[worldId] ?? "" : ""}` +
                    (levelInfo?.title && ` : ${gT(levelInfo?.title ?? "")}`)}
                  />
                {mobile?
                  // TODO: This is copied from the `Split` component below...
                  <>
                    <div className={`app-content level-mobile ${levelInfoIsLoading ? 'hidden' : ''}`}>
                      <ExercisePanel
                        codeviewRef={codeviewRef}
                        infoviewRef={infoviewRef}
                        visible={pageNumber == 0} />
                      <InventoryPanel levelInfo={levelInfo} visible={pageNumber == 1} />
                    </div>
                  </>
                :
                  <Split minSize={0} snapOffset={200} sizes={[25, 50, 25]} className={`app-content level ${levelInfoIsLoading ? 'hidden' : ''}`}>
                    <ChatPanel lastLevel={lastLevel}/>
                    <ExercisePanel
                      codeviewRef={codeviewRef}
                      infoviewRef={infoviewRef} />
                    <InventoryPanel levelInfo={levelInfo} />
                  </Split>
                }
              </MonacoEditorContext.Provider>
            </EditorContext.Provider>
  </>
}

function IntroductionPanel() {
  let { t } = useTranslation()
  const { t : gT } = useGameTranslation()
  const [gameId, navigateToGame] = useAtom(gameIdAtom)
  const [worldId] = useAtom(worldIdAtom)
  const [{ data: gameInfo }] = useAtom(gameInfoAtom)
  const [, navigateToLevel] = useAtom(levelIdAtom)

  const [mobile] = useAtom(mobileAtom)

  let text: Array<string> = gT(gameInfo?.worlds?.nodes[worldId ?? ""]?.introduction ?? "").split(/\n(\s*\n)+/)

  const focusRef = useRef<HTMLButtonElement>()
  useEffect(() => {
   focusRef.current?.focus()
  }, [])

  return <div className="chat-panel">
    <div className="chat">
      {text?.filter(t => t.trim()).map(((t, i) =>
        <Hint key={`intro-p-${i}`}
          hint={{text: t, hidden: false, rawText: t, varNames: []}} step={0} selected={null} toggleSelection={undefined} />
      ))}
    </div>
    <div className={`button-row${mobile ? ' mobile' : ''}`}>
      {gameInfo?.worldSize?.[worldId ?? ""] == 0 ?
        <Button onClick={() => {if (gameId) navigateToGame(gameId)}}>
          <FontAwesomeIcon icon={faHome} />
          </Button> :
        <Button ref={focusRef} onClick={() => navigateToLevel(1)}>
          {t("Start")}&nbsp;<FontAwesomeIcon icon={faArrowRight} />
        </Button>
      }
    </div>
  </div>
}

export default Level

/** The site with the introduction text of a world */
function Introduction() {
  let { t } = useTranslation()

  const [gameId] = useAtom(gameIdAtom)
  const [worldId] = useAtom(worldIdAtom)

  const [mobile] = useAtom(mobileAtom)

  const [{ data: inventory }] = useAtom(inventoryOverviewAtom)

  const [{ data: gameInfo, isLoading: isLoadingGameInfo }] = useAtom(gameInfoAtom)


  let image: string = worldId ? gameInfo?.worlds?.nodes[worldId]?.image ?? "" : ""

  return <>
    <LevelAppBar isLoading={isLoadingGameInfo} levelTitle={t("Introduction")} />
    {isLoadingGameInfo ?
      <div className="app-content loading"><CircularProgress /></div>
    : mobile ?
        <IntroductionPanel />
      :
        <Split minSize={0} snapOffset={200} sizes={[25, 50, 25]} className={`app-content level`}>
          <IntroductionPanel />
          <div className="world-image-container empty center">
            {image && gameId &&
              <img className="contain" src={path.join("data", gameId, image)} alt="" />
            }

          </div>
          <InventoryPanel levelInfo={inventory} />
        </Split>
      }

  </>
}
function useGetGameInfoQuery(arg0: { game: string | undefined }) {
  throw new Error('Function not implemented.')
}
