import * as React from 'react'
import type { Diagnostic, Location } from 'vscode-languageserver-protocol'

import {
    getInteractiveDiagnostics,
    getInteractiveGoals,
    getInteractiveTermGoal,
    InteractiveDiagnostic,
    InteractiveGoals,
    InteractiveTermGoal,
    isRpcError,
    LeanDiagnostic,
    RpcErrorCode,
    RpcSessionAtPos,
    UserWidgetInstance,
    Widget_getWidgets,
} from '@leanprover/infoview-api'
import { Details } from './collapsing'
import { ConfigContext, EditorContext, EnvPosContext, LspDiagnosticsContext, ProgressContext } from './contexts'
import { GoalsLocation, Locations, LocationsContext } from './goalLocation'
import { FilteredGoals, goalsToString } from './goals'
import { lspDiagToInteractive, MessagesList } from './messages'
import { RpcContext, useRpcSessionAtPos } from './rpcSessions'
import { PanelWidgetDisplay } from './userWidget'
import {
    basename,
    discardMethodNotFound,
    DocumentPosition,
    mapRpcError,
    PausableProps,
    RangeHelpers,
    useAsyncWithTrigger,
    useEvent,
    usePausableState,
} from './util'

type InfoStatus = 'updating' | 'error' | 'ready'
type InfoKind = 'cursor' | 'pin'

interface InfoPinnable {
    kind: InfoKind
    /** Takes an argument for caching reasons, but should only ever (un)pin itself. */
    onPin: (pos: DocumentPosition) => void
}

interface InfoStatusBarProps extends InfoPinnable, PausableProps {
    pos: DocumentPosition
    status: InfoStatus
    triggerUpdate: () => Promise<void>
}

const InfoStatusBar = React.memo((props: InfoStatusBarProps) => {
    const { kind, onPin, status, pos, isPaused, setPaused, triggerUpdate } = props

    const ec = React.useContext(EditorContext)

    const statusColTable: { [T in InfoStatus]: string } = {
        updating: 'gold ',
        error: 'dark-red ',
        ready: '',
    }
    const statusColor = statusColTable[status]
    const locationString = `${basename(pos.uri)}:${pos.line + 1}:${pos.character}`
    const isPinned = kind === 'pin'

    return (
        <summary style={{ transition: 'color 0.5s ease' }} className={'mv2 pointer ' + statusColor}>
            {locationString}
            {isPinned && !isPaused && ' (pinned)'}
            {!isPinned && isPaused && ' (paused)'}
            {isPinned && isPaused && ' (pinned and paused)'}
            <span
                className="fr"
                onClick={e => {
                    e.preventDefault()
                }}
            >
                {isPinned && (
                    <a
                        className="link pointer mh2 dim codicon codicon-go-to-file"
                        data-id="reveal-file-location"
                        onClick={_ => {
                            void ec.revealPosition(pos)
                        }}
                        title="reveal file location"
                    />
                )}
                <a
                    className={'link pointer mh2 dim codicon ' + (isPinned ? 'codicon-pinned ' : 'codicon-pin ')}
                    data-id="toggle-pinned"
                    onClick={_ => {
                        onPin(pos)
                    }}
                    title={isPinned ? 'unpin' : 'pin'}
                />
                <a
                    className={
                        'link pointer mh2 dim codicon ' +
                        (isPaused ? 'codicon-debug-continue ' : 'codicon-debug-pause ')
                    }
                    data-id="toggle-paused"
                    onClick={_ => {
                        setPaused(!isPaused)
                    }}
                    title={isPaused ? 'continue updating' : 'pause updating'}
                />
                <a
                    className="link pointer mh2 dim codicon codicon-refresh"
                    data-id="update"
                    onClick={_ => {
                        void triggerUpdate()
                    }}
                    title="update"
                />
            </span>
        </summary>
    )
})

interface GoalInfoDisplayProps {
    pos: DocumentPosition
    goals?: InteractiveGoals
    termGoal?: InteractiveTermGoal
    userWidgets: UserWidgetInstance[]
}

function GoalInfoDisplay(props: GoalInfoDisplayProps) {
    const { pos, goals, termGoal, userWidgets } = props

    const config = React.useContext(ConfigContext)

    const [selectedLocs, setSelectedLocs] = React.useState<GoalsLocation[]>([])

    const locs: Locations = React.useMemo(
        () => ({
            isSelected: (l: GoalsLocation) => selectedLocs.some(v => GoalsLocation.isEqual(v, l)),
            setSelected: (l, act) =>
                setSelectedLocs(ls => {
                    // We ensure that `selectedLocs` maintains its reference identity if the selection
                    // status of `l` didn't change.
                    const newLocs = ls.filter(v => !GoalsLocation.isEqual(v, l))
                    const wasSelected = newLocs.length !== ls.length
                    const isSelected = typeof act === 'function' ? act(wasSelected) : act
                    if (isSelected) newLocs.push(l)
                    return wasSelected === isSelected ? ls : newLocs
                }),
            subexprTemplate: undefined,
        }),
        [selectedLocs],
    )

    return (
        <>
            <LocationsContext.Provider value={locs}>
                <FilteredGoals key="goals" headerChildren="Tactic state" initiallyOpen goals={goals} displayCount />
            </LocationsContext.Provider>
            <FilteredGoals
                key="term-goal"
                headerChildren="Expected type"
                goals={termGoal !== undefined ? { goals: [termGoal] } : undefined}
                initiallyOpen={config.showExpectedType}
                displayCount={false}
                togglingAction="toggleExpectedType"
            />
            {userWidgets.map(widget => {
                const inner = (
                    <PanelWidgetDisplay
                        key={`widget::${widget.id}::${widget.range?.toString()}`}
                        pos={pos}
                        goals={goals ? goals.goals : []}
                        termGoal={termGoal}
                        selectedLocations={selectedLocs}
                        widget={widget}
                    />
                )
                if (widget.name)
                    return (
                        <details key={`widget::${widget.id}::${widget.range?.toString()}`} open>
                            <summary className="mv2 pointer">{widget.name}</summary>
                            {inner}
                        </details>
                    )
                else return inner
            })}
        </>
    )
}

interface InfoDisplayContentProps extends GoalInfoDisplayProps, PausableProps {
    messages: InteractiveDiagnostic[]
    error?: string
    triggerUpdate: () => Promise<void>
}

const InfoDisplayContent = React.memo((props: InfoDisplayContentProps) => {
    const { pos, messages, goals, termGoal, error, userWidgets, triggerUpdate, isPaused, setPaused } = props

    const hasWidget = userWidgets.length > 0
    const hasError = !!error
    const hasMessages = messages.length !== 0
    const nothingToShow = !hasError && !goals && !termGoal && !hasMessages && !hasWidget

    /* Adding {' '} to manage string literals properly: https://reactjs.org/docs/jsx-in-depth.html#string-literals-1 */
    return (
        <>
            {hasError && (
                <div className="error" key="errors">
                    Error updating: {error}.
                    <a
                        className="link pointer dim"
                        onClick={e => {
                            e.preventDefault()
                            void triggerUpdate()
                        }}
                    >
                        {' '}
                        Try again.
                    </a>
                </div>
            )}
            <GoalInfoDisplay
                key={DocumentPosition.toString(pos)}
                pos={pos}
                goals={goals}
                termGoal={termGoal}
                userWidgets={userWidgets}
            />
            <div style={{ display: hasMessages ? 'block' : 'none' }} key="messages">
                <Details initiallyOpen key="messages">
                    <>Messages ({messages.length})</>
                    <div className="ml1">
                        <MessagesList uri={pos.uri} messages={messages} />
                    </div>
                </Details>
            </div>
            {nothingToShow &&
                (isPaused ? (
                    /* Adding {' '} to manage string literals properly: https://reactjs.org/docs/jsx-in-depth.html#string-literals-1 */
                    <span>
                        Updating is paused.{' '}
                        <a
                            className="link pointer dim"
                            onClick={e => {
                                e.preventDefault()
                                void triggerUpdate()
                            }}
                        >
                            Refresh
                        </a>{' '}
                        or{' '}
                        <a
                            className="link pointer dim"
                            onClick={e => {
                                e.preventDefault()
                                setPaused(false)
                            }}
                        >
                            resume updating
                        </a>{' '}
                        to see information.
                    </span>
                ) : (
                    'No info found.'
                ))}
        </>
    )
})

interface InfoDisplayProps {
    pos: DocumentPosition
    status: InfoStatus
    messages: InteractiveDiagnostic[]
    goals?: InteractiveGoals
    termGoal?: InteractiveTermGoal
    error?: string
    userWidgets: UserWidgetInstance[]
    rpcSess: RpcSessionAtPos
    triggerUpdate: () => Promise<void>
}

/** Displays goal state and messages. Can be paused. */
function InfoDisplay(props0: InfoDisplayProps & InfoPinnable) {
    // Used to update the paused state *just once* if it is paused,
    // but a display update is triggered
    const [shouldRefresh, setShouldRefresh] = React.useState<boolean>(false)
    const [{ isPaused, setPaused }, props, propsRef] = usePausableState(false, props0)
    if (shouldRefresh) {
        propsRef.current = props0
        setShouldRefresh(false)
    }
    const triggerDisplayUpdate = async () => {
        await props0.triggerUpdate()
        setShouldRefresh(true)
    }

    const { kind, goals, rpcSess } = props

    const ec = React.useContext(EditorContext)

    // If we are the cursor infoview, then we should subscribe to
    // some commands from the editor extension
    const isCursor = kind === 'cursor'
    useEvent(
        ec.events.requestedAction,
        _ => {
            if (!isCursor) return
            if (goals) void ec.copyToComment(goalsToString(goals))
        },
        [isCursor, goals, ec],
        'copyToComment',
    )
    useEvent(
        ec.events.requestedAction,
        _ => {
            if (!isCursor) return
            setPaused(isPaused => !isPaused)
        },
        [isCursor, setPaused],
        'togglePaused',
    )

    return (
        <RpcContext.Provider value={rpcSess}>
            <EnvPosContext.Provider value={props.pos}>
                <details open>
                    <InfoStatusBar
                        {...props}
                        triggerUpdate={triggerDisplayUpdate}
                        isPaused={isPaused}
                        setPaused={setPaused}
                    />
                    <div className="ml1">
                        <InfoDisplayContent
                            {...props}
                            triggerUpdate={triggerDisplayUpdate}
                            isPaused={isPaused}
                            setPaused={setPaused}
                        />
                    </div>
                </details>
            </EnvPosContext.Provider>
        </RpcContext.Provider>
    )
}

/**
 * Note: in the cursor view, we have to keep the cursor position as part of the component state
 * to avoid flickering when the cursor moved. Otherwise, the component is re-initialised and the
 * goal states reset to `undefined` on cursor moves.
 */
export type InfoProps = InfoPinnable & { pos: DocumentPosition }

/** Fetches info from the server and renders an {@link InfoDisplay}. */
export function Info(props: InfoProps) {
    if (props.kind === 'cursor') return <InfoAtCursor {...props} />
    else return <InfoAux {...props} pos={props.pos} />
}

function InfoAtCursor(props: InfoProps) {
    const ec = React.useContext(EditorContext)
    // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
    const [curLoc, setCurLoc] = React.useState<Location>(ec.events.changedCursorLocation.current!)
    useEvent(ec.events.changedCursorLocation, loc => loc && setCurLoc(loc), [])
    const pos = { uri: curLoc.uri, ...curLoc.range.start }
    return <InfoAux {...props} pos={pos} />
}

function useIsProcessingAt(p: DocumentPosition): boolean {
    const allProgress = React.useContext(ProgressContext)
    const processing = allProgress.get(p.uri)
    if (!processing) return false
    return processing.some(i => RangeHelpers.contains(i.range, p))
}

function InfoAux(props: InfoProps) {
    const config = React.useContext(ConfigContext)

    const pos = props.pos
    const rpcSess = useRpcSessionAtPos(pos)

    // Compute the LSP diagnostics at this info's position. We try to ensure that if these remain
    // the same, then so does the identity of `lspDiagsHere` so that it can be used as a dep.
    const lspDiags = React.useContext(LspDiagnosticsContext)
    const [lspDiagsHere, setLspDiagsHere] = React.useState<Diagnostic[]>([])
    React.useEffect(() => {
        // Note: the curly braces are important. https://medium.com/geekculture/react-uncaught-typeerror-destroy-is-not-a-function-192738a6e79b
        setLspDiagsHere(diags0 => {
            const diagPred = (d: Diagnostic) =>
                RangeHelpers.contains(
                    (d as LeanDiagnostic).fullRange || d.range,
                    { line: pos.line, character: pos.character },
                    config.allErrorsOnLine,
                )
            const newDiags = (lspDiags.get(pos.uri) || []).filter(diagPred)
            if (newDiags.length === diags0.length && newDiags.every((d, i) => d === diags0[i])) return diags0
            return newDiags
        })
    }, [lspDiags, pos.uri, pos.line, pos.character, config.allErrorsOnLine])

    const serverIsProcessing = useIsProcessingAt(pos)

    // This is a virtual dep of the info-requesting function. It is bumped whenever the Lean server
    // indicates that another request should be made. Bumping it dirties the dep state of
    // `useAsyncWithTrigger` below, causing the `useEffect` lower down in this component to
    // make the request. We cannot simply call `triggerUpdateCore` because `useAsyncWithTrigger`
    // does not support reentrancy like that.
    const [updaterTick, setUpdaterTick] = React.useState<number>(0)

    // For atomicity, we use a single update function that fetches all the info at `pos` at once.
    // Besides what the server replies with, we also include the inputs (deps) in this type so
    // that the displayed state cannot ever get out of sync by showing an old reply together
    // with e.g. a new `pos`.
    type InfoRequestResult = Omit<InfoDisplayProps, 'triggerUpdate'>
    const [state, triggerUpdateCore] = useAsyncWithTrigger(
        () =>
            new Promise<InfoRequestResult>((resolve, reject) => {
                const goalsReq = getInteractiveGoals(rpcSess, DocumentPosition.toTdpp(pos))
                const termGoalReq = getInteractiveTermGoal(rpcSess, DocumentPosition.toTdpp(pos))
                const widgetsReq = Widget_getWidgets(rpcSess, pos).catch(discardMethodNotFound)
                const messagesReq = getInteractiveDiagnostics(rpcSess, { start: pos.line, end: pos.line + 1 })
                    // fall back to non-interactive diagnostics when lake fails
                    // (see https://github.com/leanprover/vscode-lean4/issues/90)
                    .then(diags => (diags.length === 0 ? lspDiagsHere.map(lspDiagToInteractive) : diags))

                // While `lake print-paths` is running, the output of Lake is shown as
                // info diagnostics on line 1.  However, all RPC requests block until
                // Lake is finished, so we don't see these diagnostics while Lake is
                // building. Therefore we show the LSP diagnostics on line 1 if the
                // server does not respond within half a second.
                // The same is true for fatal header diagnostics like the stale dependency notification.
                const isAllHeaderDiags =
                    lspDiagsHere.length > 0 && lspDiagsHere.every(diag => diag.range.start.line === 0)
                if (isAllHeaderDiags) {
                    setTimeout(
                        () =>
                            resolve({
                                pos,
                                status: 'updating',
                                messages: lspDiagsHere.map(lspDiagToInteractive),
                                goals: undefined,
                                termGoal: undefined,
                                error: undefined,
                                userWidgets: [],
                                rpcSess,
                            }),
                        500,
                    )
                }

                // NB: it is important to await await reqs at once, otherwise
                // if both throw then one exception becomes unhandled.
                Promise.all([goalsReq, termGoalReq, widgetsReq, messagesReq]).then(
                    ([goals, termGoal, userWidgets, messages]) =>
                        resolve({
                            pos,
                            status: 'ready',
                            messages,
                            goals,
                            termGoal,
                            error: undefined,
                            userWidgets: userWidgets?.widgets ?? [],
                            rpcSess,
                        }),
                    ex => {
                        if (ex?.code === RpcErrorCode.ContentModified || ex?.code === RpcErrorCode.RpcNeedsReconnect) {
                            // Document has been changed since we made the request, or we need to reconnect
                            // to the RPC sessions. Try again.
                            setUpdaterTick(t => t + 1)
                            reject('retry')
                        }

                        let errorString = ''
                        if (typeof ex === 'string') {
                            errorString = ex
                        } else if (isRpcError(ex)) {
                            errorString = mapRpcError(ex).message
                        } else if (ex instanceof Error) {
                            errorString = ex.toString()
                        } else {
                            errorString = `Unrecognized error: ${JSON.stringify(ex)}`
                        }

                        resolve({
                            pos,
                            status: 'error',
                            messages: lspDiagsHere.map(lspDiagToInteractive),
                            goals: undefined,
                            termGoal: undefined,
                            error: `Error fetching goals: ${errorString}`,
                            userWidgets: [],
                            rpcSess,
                        })
                    },
                )
            }),
        [updaterTick, pos.uri, pos.line, pos.character, rpcSess, serverIsProcessing, lspDiagsHere],
    )

    // We use a timeout to debounce info requests. Whenever a request is already scheduled
    // but something happens that warrants a request for newer info, we cancel the old request
    // and schedule just the new one.
    const updaterTimeout = React.useRef<number>()
    const clearUpdaterTimeout = () => {
        if (updaterTimeout.current) {
            window.clearTimeout(updaterTimeout.current)
            updaterTimeout.current = undefined
        }
    }
    const triggerUpdate = React.useCallback(
        () =>
            new Promise<void>(resolve => {
                clearUpdaterTimeout()
                const tm = window.setTimeout(() => {
                    void triggerUpdateCore().then(resolve)
                    updaterTimeout.current = undefined
                }, config.debounceTime)
                // Hack: even if the request is cancelled, the promise should resolve so that no `await`
                // is left waiting forever. We ensure this happens in a simple way.
                window.setTimeout(resolve, config.debounceTime)
                updaterTimeout.current = tm
            }),
        [triggerUpdateCore, config.debounceTime],
    )

    const [displayProps, setDisplayProps] = React.useState<InfoDisplayProps>({
        pos,
        status: 'updating',
        messages: [],
        goals: undefined,
        termGoal: undefined,
        error: undefined,
        userWidgets: [],
        rpcSess,
        triggerUpdate,
    })

    // Propagates changes in the state of async info requests to the display props,
    // and re-requests info if needed.
    // This effect triggers new requests for info whenever need. It also propagates changes
    // in the state of the `useAsyncWithTrigger` to the displayed props.
    React.useEffect(() => {
        if (state.state === 'notStarted') void triggerUpdate()
        else if (state.state === 'loading') setDisplayProps(dp => ({ ...dp, status: 'updating' }))
        else if (state.state === 'resolved') {
            setDisplayProps({ ...state.value, triggerUpdate })
        } else if (state.state === 'rejected' && state.error !== 'retry') {
            // The code inside `useAsyncWithTrigger` may only ever reject with a `retry` exception.
            console.warn('Unreachable code reached with error: ', state.error)
        }
    }, [state, triggerUpdate])

    return <InfoDisplay kind={props.kind} onPin={props.onPin} {...displayProps} />
}
