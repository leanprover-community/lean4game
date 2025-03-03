/* eslint-disable @typescript-eslint/no-namespace */
/* eslint-disable react-hooks/exhaustive-deps */
import * as React from 'react'
import type { DocumentUri, Position, Range, TextDocumentPositionParams } from 'vscode-languageserver-protocol'

import { isRpcError, RpcErrorCode } from '@leanprover/infoview-api'

import { EditorContext } from './contexts'
import { EventEmitter } from './event'

/** A document URI and a position in that document. */
export interface DocumentPosition extends Position {
    uri: DocumentUri
}

export namespace DocumentPosition {
    export function isEqual(p1: DocumentPosition, p2: DocumentPosition): boolean {
        return p1.uri === p2.uri && p1.line === p2.line && p1.character === p2.character
    }

    export function toTdpp(p: DocumentPosition): TextDocumentPositionParams {
        return { textDocument: { uri: p.uri }, position: { line: p.line, character: p.character } }
    }

    export function toString(p: DocumentPosition) {
        return `${p.uri}:${p.line + 1}:${p.character}`
    }
}

export namespace PositionHelpers {
    export function isLessThanOrEqual(p1: Position, p2: Position): boolean {
        return p1.line < p2.line || (p1.line === p2.line && p1.character <= p2.character)
    }
}

export namespace RangeHelpers {
    export function contains(range: Range, pos: Position, ignoreCharacter?: boolean): boolean {
        if (!ignoreCharacter) {
            if (pos.line === range.start.line && pos.character < range.start.character) return false
            if (pos.line === range.end.line && pos.character > range.end.character) return false
        }
        return range.start.line <= pos.line && pos.line <= range.end.line
    }
}

// https://stackoverflow.com/questions/6234773/can-i-escape-html-special-chars-in-javascript
export function escapeHtml(s: string): string {
    return s
        .replace(/&/g, '&amp;')
        .replace(/</g, '&lt;')
        .replace(/>/g, '&gt;')
        .replace(/"/g, '&quot;')
        .replace(/'/g, '&#039;')
}

/** @deprecated (unused) */
export function colorizeMessage(goal: string): string {
    return goal
        .replace(/^([|⊢]) /gm, '<strong class="goal-vdash">$1</strong> ')
        .replace(/^(\d+ goals|1 goal)/gm, '<strong class="goal-goals">$1</strong>')
        .replace(/^(context|state):/gm, '<strong class="goal-goals">$1</strong>:')
        .replace(/^(case) /gm, '<strong class="goal-case">$1</strong> ')
        .replace(/^([^:\n< ][^:\n⊢{[(⦃]*) :/gm, '<strong class="goal-hyp">$1</strong> :')
}

export function basename(path: string): string {
    const bn = path.split(/[\\/]/).pop()
    if (bn) return bn
    else return ''
}

/**
 * A specialization of {@link React.useEffect} which executes `f` with the event data
 * whenever `ev` fires.
 * If `key` is provided, `f` is only invoked on events fired with that key.
 */
export function useEvent<E, K>(
    ev: EventEmitter<E, K>,
    f: (_: E) => void,
    dependencies?: React.DependencyList,
    key?: K,
): void {
    React.useEffect(() => {
        const h = ev.on(f, key)
        return () => h.dispose()
    }, dependencies)
}

/**
 * A piece of React {@link React.useState} which returns the data that `ev` most recently fired with.
 * If `f` is provided, the data is mapped through `f` first. */
export function useEventResult<E, K>(ev: EventEmitter<E, K>): E | undefined
export function useEventResult<E, K, T>(ev: EventEmitter<E, K>, f: (newVal: E) => T): T | undefined
export function useEventResult<E, K, T>(ev: EventEmitter<E, K>, f?: (_: E) => T): T | undefined {
    const fn: (_: E) => T = f ?? (x => x as any)
    const [s, setS] = React.useState<T | undefined>(ev.current ? fn(ev.current) : undefined)
    useEvent<E, K>(ev, newV => setS(newV ? fn(newV) : undefined))
    return s
}

export function useServerNotificationEffect<T>(
    method: string,
    f: (params: T) => void,
    deps?: React.DependencyList,
): void {
    const ec = React.useContext(EditorContext)
    React.useEffect(() => {
        void ec.api.subscribeServerNotifications(method).catch(ex => {
            console.error(`Failed subscribing to server notification '${method}': ${ex}`)
        })
        const h = ec.events.gotServerNotification.on(([thisMethod, params]: [string, T]) => {
            if (thisMethod !== method) return
            f(params)
        })
        return () => {
            h.dispose()
            void ec.api.unsubscribeServerNotifications(method)
        }
    }, deps)
}

/**
 * Returns the same tuple as `setState` such that whenever a server notification with `method`
 * arrives at the editor, the state will be updated according to `f`.
 */
export function useServerNotificationState<S, T>(
    method: string,
    initial: S,
    f: (params: T) => Promise<(state: S) => S>,
    deps?: React.DependencyList,
): [S, React.Dispatch<React.SetStateAction<S>>] {
    const [s, setS] = React.useState<S>(initial)

    useServerNotificationEffect(method, (params: T) => void f(params).then(g => setS(g)), deps)

    return [s, setS]
}

export function useClientNotificationEffect<T>(
    method: string,
    f: (params: T) => void,
    deps?: React.DependencyList,
): void {
    const ec = React.useContext(EditorContext)
    React.useEffect(() => {
        void ec.api.subscribeClientNotifications(method).catch(ex => {
            console.error(`Failed subscribing to client notification '${method}': ${ex}`)
        })
        const h = ec.events.sentClientNotification.on(([thisMethod, params]: [string, T]) => {
            if (thisMethod !== method) return
            f(params)
        })
        return () => {
            h.dispose()
            void ec.api.unsubscribeClientNotifications(method)
        }
    }, deps)
}

/**
 * Like {@link useServerNotificationState} but for client->server notifications sent by the editor.
 */
export function useClientNotificationState<S, T>(
    method: string,
    initial: S,
    f: (state: S, params: T) => S,
    deps?: React.DependencyList,
): [S, React.Dispatch<React.SetStateAction<S>>] {
    const [s, setS] = React.useState<S>(initial)

    useClientNotificationEffect(
        method,
        (params: T) => {
            setS(state => f(state, params))
        },
        deps,
    )

    return [s, setS]
}

/** Useful for controlling {@link usePausableState} from child components. */
export interface PausableProps {
    isPaused: boolean
    setPaused: React.Dispatch<React.SetStateAction<boolean>>
}

/**
 * Returns `[{ isPaused, setPaused }, tPausable, tRef]` s.t.
 * - `[isPaused, setPaused]` are the paused status state
 * - for as long as `isPaused` is set, `tPausable` holds its initial value (the `t` passed before pausing)
 *   rather than updates with changes to `t`.
 * - `tRef` can be used to overwrite the paused state
 *
 * To pause child components, `startPaused` can be passed in their props.
 */
export function usePausableState<T>(startPaused: boolean, t: T): [PausableProps, T, React.MutableRefObject<T>] {
    const [isPaused, setPaused] = React.useState<boolean>(startPaused)
    const old = React.useRef<T>(t)
    if (!isPaused) old.current = t
    return [{ isPaused, setPaused }, old.current, old]
}

export type Keyed<T> = T & { key: string }

/**
 * Adds a unique `key` property to each element in `elems` using
 * the values of (possibly non-injective) `getId`.
 */
export function addUniqueKeys<T>(elems: T[], getId: (el: T) => string): Keyed<T>[] {
    const keys: { [key: string]: number } = {}
    return elems.map(el => {
        const id = getId(el)
        keys[id] = (keys[id] || 0) + 1
        return { key: `${id}:${keys[id]}`, ...el }
    })
}

export interface LogicalDomElement {
    contains(el: Node): boolean
}

export interface LogicalDomStorage {
    /** Registers a descendant in the logical DOM.
     * Returns a function which disposes of the registration. */
    registerDescendant(el: LogicalDomElement): () => void
}

export const LogicalDomContext = React.createContext<LogicalDomStorage>({ registerDescendant: () => () => {} })

/** Suppose a component B appears as a React descendant of the component A. For layout reasons,
 * we sometimes don't want B to appear as a descendant of A in the DOM, so we use `createPortal`.
 * We may still however want to carry out `contains` checks as if B were there, i.e. according to
 * the React tree structure rather than the DOM structure. While React already correctly propagates
 * DOM events up the React tree, other functionality such as `contains` is not provided. We provide
 * it in this hook.
 *
 * Accepts a ref to the observed {@link HTMLElement} (A in the example). Returns:
 * - a {@link LogicalDomElement} which provides `contains` checks for that {@link HTMLElement}; and
 * - a {@link LogicalDomStorage} which MUST be passed to a {@link LogicalDomContext} enclosing
 *   the observed {@link HTMLElement}.
 *
 * Additionally, any component which introduces a portal MUST call `registerDescendant` in the
 * {@link LogicalDomContext} with a ref to the portalled component (B in the example). */
export function useLogicalDomObserver(elt: React.RefObject<HTMLElement>): [LogicalDomElement, LogicalDomStorage] {
    const parentCtx = React.useContext(LogicalDomContext)
    const descendants = React.useRef<Set<LogicalDomElement>>(new Set())

    // Provides a `contains` check for the children only, but not the observed element.
    // We pass this to the parent context under the assumption that its own DOM-based
    // `contains` check already includes the observed element.
    const logicalChildrenElt = React.useMemo(
        () => ({
            contains: (e: Node) => {
                for (const d of descendants.current) {
                    if (d.contains(e)) return true
                }
                return false
            },
        }),
        [],
    )

    React.useEffect(() => parentCtx.registerDescendant(logicalChildrenElt), [parentCtx, logicalChildrenElt])

    const logicalElt = React.useMemo(
        () => ({
            contains: (e: Node) => {
                if (!elt.current) return false
                if (elt.current.contains(e)) return true
                return logicalChildrenElt.contains(e)
            },
        }),
        [elt, logicalChildrenElt],
    )

    const registerDescendant = React.useCallback((el: LogicalDomElement) => {
        descendants.current.add(el)
        return () => {
            descendants.current.delete(el)
        }
    }, [])

    return [logicalElt, React.useMemo(() => ({ registerDescendant }), [registerDescendant])]
}

/**
 * An effect which calls `onClickOutside` whenever an element not logically descending from `ld`
 * (see {@link useLogicalDomObserver}) is clicked. Note that `onClickOutside` is not called on clicks
 * on the scrollbar since these should usually not impact the app's state.
 * `isActive` controls whether the `onClickOutside` handler is active. This can be useful for performance,
 * since having lots of `onClickOutside` handlers when they are not needed can be expensive.
 */
export function useOnClickOutside(
    ld: LogicalDomElement,
    onClickOutside: (_: PointerEvent) => void,
    isActive: boolean = true,
) {
    React.useEffect(() => {
        if (!isActive) {
            return
        }
        const onClickAnywhere = (e: PointerEvent) => {
            if (e.target instanceof Node && !ld.contains(e.target)) {
                if (e.target instanceof Element && e.target.tagName === 'HTML') {
                    // then user might be clicking in a scrollbar, otherwise
                    // e.target would be a tag other than 'HTML'
                } else onClickOutside(e)
            }
        }

        document.addEventListener('pointerdown', onClickAnywhere)
        return () => document.removeEventListener('pointerdown', onClickAnywhere)
    }, [ld, onClickOutside, isActive])
}

/** Sends an exception object to a throwable error.
 * Maps JSON Rpc errors to throwable errors.
 */
export function mapRpcError(err: unknown): Error {
    if (isRpcError(err)) {
        return new Error(`Rpc error: ${RpcErrorCode[err.code]}: ${err.message}`)
    } else if (!(err instanceof Error)) {
        return new Error(`Unrecognised error ${JSON.stringify(err)}`)
    } else {
        return err
    }
}

/** Catch handler for RPC methods that just returns undefined if the method is not found.
 * This is useful for compatibility with versions of Lean that do not yet have the given RPC method.
 */
export function discardMethodNotFound(e: unknown): undefined {
    if (isRpcError(e) && e.code === RpcErrorCode.MethodNotFound) {
        return undefined
    } else {
        throw mapRpcError(e)
    }
}

export type AsyncState<T> = { state: 'loading' } | { state: 'resolved'; value: T } | { state: 'rejected'; error: any }

export type AsyncWithTriggerState<T> = { state: 'notStarted' } | AsyncState<T>

export function useAsyncWithTrigger<T>(
    fn: () => Promise<T>,
    deps: React.DependencyList = [],
): [AsyncWithTriggerState<T>, () => Promise<void>] {
    const asyncState = React.useRef<AsyncWithTriggerState<T>>({ state: 'notStarted' })
    const asyncStateDeps = React.useRef<React.DependencyList>([])
    // A monotonically increasing counter.
    const tick = React.useRef(0)
    // This is bumped up to the current `tick` whenever `asyncState.current` is assigned,
    // in order to trigger a React update.
    const [_, setUpdate] = React.useState(0)

    const trigger = React.useCallback(async () => {
        if (asyncState.current.state === 'loading' || asyncState.current.state === 'resolved') return

        tick.current += 1
        asyncState.current = { state: 'loading' }
        setUpdate(tick.current)

        tick.current += 1
        const startTick = tick.current
        const set = (state: AsyncWithTriggerState<T>) => {
            if (tick.current === startTick) {
                asyncState.current = state
                setUpdate(tick.current)
            }
        }
        return fn().then(
            value => set({ state: 'resolved', value }),
            error => set({ state: 'rejected', error }),
        )
    }, deps)

    const depsTheSame =
        asyncStateDeps.current.length === deps.length && asyncStateDeps.current.every((d, i) => Object.is(d, deps[i]))
    if (!depsTheSame) {
        tick.current += 1
        asyncState.current = { state: 'notStarted' }
        asyncStateDeps.current = deps
        setUpdate(tick.current)
    }
    return [asyncState.current, trigger]
}

/** This React hook will run the given promise function `fn` whenever the deps change
 * and use it to update the status and result when the promise resolves.
 *
 * This function prevents race conditions if the requests resolve in a
 * different order to that which they were requested in:
 *
 * - Request 1 is sent with, say, line=42.
 * - Request 2 is sent with line=90.
 * - Request 2 returns with diags=[].
 * - Request 1 returns with diags=['error'].
 *
 * Without `useAsync` we would now return the diagnostics for line 42 even though we're at line 90.
 *
 * When the deps change, the function immediately returns `{ state: 'loading' }`.
 */
export function useAsync<T>(fn: () => Promise<T>, deps: React.DependencyList = []): AsyncState<T> {
    const [state, trigger] = useAsyncWithTrigger(fn, deps)
    if (state.state === 'notStarted') {
        void trigger()
        return { state: 'loading' }
    } else {
        return state
    }
}

/** Like {@link useAsync} but never transitions from `resolved` to `loading` by internally storing
 * the latest `resolved` state and continuing to return it while an update is in flight. The lower
 * amount of re-renders tends to be less visually jarring.
 */
export function useAsyncPersistent<T>(fn: () => Promise<T>, deps: React.DependencyList = []): AsyncState<T> {
    const [latestState, setLatestState] = React.useState<T | undefined>(undefined)
    const state = useAsync(async () => {
        const newState = await fn()
        setLatestState(newState)
        return newState
    }, deps)
    if (state.state === 'loading' && latestState !== undefined) {
        return { state: 'resolved', value: latestState }
    }
    return state
}
