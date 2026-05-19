import type { DocumentUri, Position, Range, TextDocumentPositionParams } from 'vscode-languageserver-protocol'
import { EventEmitter } from './event'
import React from 'react'

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
