import * as React from 'react'
import {
    DidChangeTextDocumentParams,
    DidCloseTextDocumentParams,
    TextDocumentContentChangeEvent,
} from 'vscode-languageserver-protocol'

import { EditorContext } from './contexts'
import { Info, InfoProps } from './info'
import {
    DocumentPosition,
    Keyed,
    PositionHelpers,
    useClientNotificationEffect,
    useClientNotificationState,
    useEvent,
    useEventResult,
} from './util'

function isPinned(pinnedPositions: DocumentPosition[], pos: DocumentPosition): boolean {
    return pinnedPositions.some(p => DocumentPosition.isEqual(p, pos))
}

/** Manages and displays pinned infos, as well as info for the current location. */
export function Infos() {
    const ec = React.useContext(EditorContext)

    // Update pins when the document changes. In particular, when edits are made
    // earlier in the text such that a pin has to move up or down.
    const [pinnedPositions, setPinnedPositions] = useClientNotificationState(
        'textDocument/didChange',
        new Array<Keyed<DocumentPosition>>(),
        (pinnedPositions, params: DidChangeTextDocumentParams) => {
            if (pinnedPositions.length === 0) return pinnedPositions

            let changed: boolean = false
            const newPins = pinnedPositions.map(pin => {
                if (pin.uri !== params.textDocument.uri) return pin
                // NOTE(WN): It's important to make a clone here, otherwise this
                // actually mutates the pin. React state updates must be pure.
                // See https://github.com/facebook/react/issues/12856
                const newPin: Keyed<DocumentPosition> = { ...pin }
                for (const chg of params.contentChanges) {
                    if (!TextDocumentContentChangeEvent.isIncremental(chg)) {
                        changed = true
                        return null
                    }
                    if (PositionHelpers.isLessThanOrEqual(newPin, chg.range.start)) continue
                    // We can assume chg.range.start < pin

                    // If the pinned position is replaced with new text, just delete the pin.
                    if (PositionHelpers.isLessThanOrEqual(newPin, chg.range.end)) {
                        changed = true
                        return null
                    }

                    const oldPin = { ...newPin }

                    // How many lines before the pin position were added by the change.
                    // Can be negative when more lines are removed than added.
                    let additionalLines = 0
                    let lastLineLen = chg.range.start.character
                    for (const c of chg.text)
                        if (c === '\n') {
                            additionalLines++
                            lastLineLen = 0
                        } else lastLineLen++

                    // Subtract lines that were already present
                    additionalLines -= chg.range.end.line - chg.range.start.line
                    newPin.line += additionalLines

                    if (oldPin.line < chg.range.end.line) {
                        // Should never execute by the <= check above.
                        throw new Error('unreachable code reached')
                    } else if (oldPin.line === chg.range.end.line) {
                        newPin.character = lastLineLen + (oldPin.character - chg.range.end.character)
                    }
                }
                if (!DocumentPosition.isEqual(newPin, pin)) changed = true

                // NOTE(WN): We maintain the `key` when a pin is moved around to maintain
                // its component identity and minimise flickering.
                return newPin
            })

            if (changed) return newPins.filter(p => p !== null) as Keyed<DocumentPosition>[]
            return pinnedPositions
        },
        [],
    )

    // Remove pins for closed documents
    useClientNotificationEffect(
        'textDocument/didClose',
        (params: DidCloseTextDocumentParams) => {
            setPinnedPositions(pinnedPositions => pinnedPositions.filter(p => p.uri !== params.textDocument.uri))
        },
        [],
    )

    const curPos: DocumentPosition | undefined = useEventResult(ec.events.changedCursorLocation, loc =>
        loc ? { uri: loc.uri, ...loc.range.start } : undefined,
    )

    // Update pins on UI actions
    const pinKey = React.useRef<number>(0)
    const pin = React.useCallback(
        (pos: DocumentPosition) => {
            setPinnedPositions(pinnedPositions => {
                if (isPinned(pinnedPositions, pos)) return pinnedPositions
                pinKey.current += 1
                return [...pinnedPositions, { ...pos, key: pinKey.current.toString() }]
            })
        },
        [setPinnedPositions],
    )
    const unpin = React.useCallback(
        (pos: DocumentPosition) => {
            setPinnedPositions(pinnedPositions => {
                if (!isPinned(pinnedPositions, pos)) return pinnedPositions
                return pinnedPositions.filter(p => !DocumentPosition.isEqual(p, pos))
            })
        },
        [setPinnedPositions],
    )

    // Toggle pin at current position when the editor requests it
    useEvent(
        ec.events.requestedAction,
        _ => {
            if (!curPos) return
            setPinnedPositions(pinnedPositions => {
                if (isPinned(pinnedPositions, curPos)) {
                    return pinnedPositions.filter(p => !DocumentPosition.isEqual(p, curPos))
                } else {
                    pinKey.current += 1
                    return [...pinnedPositions, { ...curPos, key: pinKey.current.toString() }]
                }
            })
        },
        [curPos?.uri, curPos?.line, curPos?.character, setPinnedPositions, pinKey],
        'togglePin',
    )

    const infoProps: Keyed<InfoProps>[] = pinnedPositions.map(pos => ({ kind: 'pin', onPin: unpin, pos, key: pos.key }))
    if (curPos) infoProps.push({ kind: 'cursor', onPin: pin, key: 'cursor', pos: curPos })

    return (
        <div>
            {infoProps.map(ps => (
                <Info {...ps} key={ps.key} />
            ))}
            {!curPos && <p>Click somewhere in the Lean file to enable the infoview.</p>}
        </div>
    )
}
