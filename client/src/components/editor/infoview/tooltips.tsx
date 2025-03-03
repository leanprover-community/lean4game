import * as React from 'react'
import * as ReactDOM from 'react-dom'

import { arrow, autoPlacement, autoUpdate, FloatingArrow, offset, shift, size, useFloating } from '@floating-ui/react'

import { ConfigContext } from './contexts'
import { LogicalDomContext, useLogicalDomObserver, useOnClickOutside } from './util'

export type TooltipProps = React.PropsWithChildren<React.HTMLProps<HTMLDivElement>> & { reference: HTMLElement | null }

export function Tooltip(props_: TooltipProps) {
    const { reference, children, style, ...props } = props_
    const arrowRef = React.useRef(null)

    const { refs, floatingStyles, context } = useFloating({
        elements: { reference },
        placement: 'top',
        middleware: [
            offset(8),
            shift(),
            autoPlacement({
                padding: 10,
            }),
            size({
                apply({ availableHeight, elements }) {
                    elements.floating.style.maxHeight = `${Math.min(availableHeight, 300)}px`
                },
                padding: 10,
            }),
            // NOTE: `padding` should be `tooltip.borderRadius` or more so that the arrow
            // doesn't overflow the rounded corner.
            arrow({ element: arrowRef, padding: 6 }),
        ],
        whileElementsMounted: autoUpdate,
    })

    const logicalDom = React.useContext(LogicalDomContext)
    const logicalDomCleanupFn = React.useRef<() => void>(() => {})
    const floating = (
        <div
            ref={node => {
                refs.setFloating(node)
                logicalDomCleanupFn.current()
                if (node) logicalDomCleanupFn.current = logicalDom.registerDescendant(node)
                else logicalDomCleanupFn.current = () => {}
            }}
            style={{ ...style, ...floatingStyles }}
            className="tooltip"
            {...props}
        >
            <FloatingArrow
                ref={arrowRef}
                context={context}
                fill="var(--vscode-editorHoverWidget-background)"
                strokeWidth={1}
                stroke="var(--vscode-editorHoverWidget-border)"
            />
            <div className="tooltip-content">{children}</div>
        </div>
    )

    // Append the tooltip to the end of document body to avoid layout issues.
    // (https://github.com/leanprover/vscode-lean4/issues/51)
    return ReactDOM.createPortal(floating, document.body)
}

export interface ToggleableTooltip {
    tooltip: JSX.Element
    tooltipDisplayed: boolean
    setTooltipDisplayed: (tooltipDisplayed: boolean) => void
    onClick: () => void
    onClickOutside: () => void
}

/**
 * Provides handlers to show a tooltip when a state variable is changed.
 * The tooltip is hidden when a click is made anywhere (on or outside the tooltip).
 */
export function useToggleableTooltip(
    ref: React.RefObject<HTMLSpanElement>,
    tooltipChildren: React.ReactNode,
): ToggleableTooltip {
    const [anchor, setAnchor] = React.useState<HTMLSpanElement | null>(null)
    const [tooltipDisplayed, setTooltipDisplayed_] = React.useState<boolean>(false)
    const setTooltipDisplayed = (tooltipDisplayed: boolean) => {
        setTooltipDisplayed_(tooltipDisplayed)
        if (tooltipDisplayed) {
            // Setting the tooltip anchor lazily only when the tooltip is displayed avoids accidental
            // re-renders induced by setting this state variable during the initial render of a component.
            setAnchor(ref.current)
        }
    }

    // Since we do not want to hide the tooltip if the user is trying to select text in it,
    // we need both the "click outside" and "click inside" handlers here because they
    // play nicer with existing selections than a global click handler.
    // With a single global click handler, any selection anywhere in the InfoView could block
    // the tooltip from being hidden. This is especially annoying because right-clicking any
    // element also selects it.
    // With both inside and outside click handlers, the outside click handler can simply disregard
    // selections, whereas React ensures that only a selection in the tooltip itself can block
    // the inside click handler from hiding the tooltip, since the outer selection is removed
    // before the inside click handler fires.
    const onClickOutside = () => {
        setTooltipDisplayed(false)
    }

    const onClick = () => {
        if (!window.getSelection()?.toString()) {
            setTooltipDisplayed(false)
        }
    }

    const tooltip = <>{tooltipDisplayed && <Tooltip reference={anchor}>{tooltipChildren}</Tooltip>}</>

    return {
        tooltip,
        tooltipDisplayed,
        setTooltipDisplayed,
        onClick,
        onClickOutside,
    }
}

/** Hover state of an element. The pointer can be
 * - elsewhere (`off`)
 * - over the element (`over`)
 * - over the element with Ctrl or Meta (⌘ on Mac) held (`ctrlOver`)
 */
export type HoverState = 'off' | 'over' | 'ctrlOver'

/** Pinning a child tooltip has to also pin all ancestors. This context supports that. */
interface TipChainContext {
    pinParent(): void
}

const TipChainContext = React.createContext<TipChainContext>({ pinParent: () => {} })

// We are pinned when clicked, shown when hovered over, and otherwise hidden.
export type TooltipState = 'pin' | 'show' | 'hide'

export interface HoverTooltip {
    state: TooltipState
    onClick: (e: React.MouseEvent<HTMLSpanElement>) => void
    onClickOutside: () => void
    onPointerDown: (e: React.PointerEvent<HTMLSpanElement>) => void
    onPointerOver: (e: React.PointerEvent<HTMLSpanElement>) => void
    onPointerOut: (e: React.PointerEvent<HTMLSpanElement>) => void
    tooltip: JSX.Element
}

/** Provides handlers to show a tooltip when the children of a component are hovered over or clicked.
 *
 * A `guardedOnClick` middleware can optionally be given in order to control what happens when the
 * hoverable area is clicked. The middleware can invoke `cont` to execute the default action,
 * which is to pin the tooltip open.
 */
export function useHoverTooltip(
    ref: React.RefObject<HTMLSpanElement>,
    tooltipChildren: React.ReactNode,
    guardedOnClick?: (
        e: React.MouseEvent<HTMLSpanElement, MouseEvent>,
        cont: (e: React.MouseEvent<HTMLSpanElement, MouseEvent>) => void,
    ) => void,
): HoverTooltip {
    const config = React.useContext(ConfigContext)

    const [state, setState_] = React.useState<TooltipState>('hide')
    const [anchor, setAnchor] = React.useState<HTMLSpanElement | null>(null)
    const setState: (state: TooltipState) => void = React.useCallback(
        state => {
            setState_(state)
            if (state !== 'hide') {
                setAnchor(ref.current)
            }
        },
        [ref],
    )

    const tipChainCtx = React.useContext(TipChainContext)
    React.useEffect(() => {
        if (state === 'pin') tipChainCtx.pinParent()
    }, [state, tipChainCtx])
    const newHTTipChainCtx = React.useMemo(
        () => ({
            pinParent: () => {
                setState('pin')
                tipChainCtx.pinParent()
            },
        }),
        [tipChainCtx, setState],
    )

    // Note: because tooltips are attached to `document.body`, they are not descendants of the
    // hoverable area in the DOM tree. Thus the `contains` check fails for elements within tooltip
    // contents and succeeds for elements within the hoverable. We can use this to distinguish them.
    const isWithinHoverable = (el: EventTarget) => ref.current && el instanceof Node && ref.current.contains(el)

    // We use timeouts for debouncing hover events.
    const timeout = React.useRef<number>()
    const clearTimeout = () => {
        if (timeout.current) {
            window.clearTimeout(timeout.current)
            timeout.current = undefined
        }
    }

    const showDelay = 500
    const hideDelay = 300

    const startShowTimeout = () => {
        clearTimeout()
        if (!config.showTooltipOnHover) return
        timeout.current = window.setTimeout(() => {
            setState(state === 'hide' ? 'show' : state)
            timeout.current = undefined
        }, showDelay)
    }

    const isPointerOverTooltip = React.useRef<boolean>(false)

    const startHideTimeout = () => {
        clearTimeout()
        timeout.current = window.setTimeout(() => {
            if (!isPointerOverTooltip.current) setState(state === 'show' ? 'hide' : state)
            timeout.current = undefined
        }, hideDelay)
    }

    const onPointerEnter = (e: React.PointerEvent<HTMLSpanElement>) => {
        isPointerOverTooltip.current = true
        clearTimeout()
    }

    const onPointerLeave = (e: React.PointerEvent<HTMLSpanElement>) => {
        isPointerOverTooltip.current = false
        startHideTimeout()
    }

    const guardMouseEvent = (
        act: (_: React.MouseEvent<HTMLSpanElement>) => void,
        e: React.MouseEvent<HTMLSpanElement>,
    ) => {
        if ('_WithTooltipOnHoverSeen' in e) return
        if (!isWithinHoverable(e.target)) return
        ;(e as any)._WithTooltipOnHoverSeen = {}
        act(e)
    }

    const pinClick = (e: React.MouseEvent<HTMLSpanElement>) => {
        clearTimeout()
        setState(state === 'pin' ? 'hide' : 'pin')
        e.stopPropagation()
        e.preventDefault()
    }

    const onClick = (e: React.MouseEvent<HTMLSpanElement>) => {
        guardMouseEvent(e => {
            if (!guardedOnClick) {
                pinClick(e)
                return
            }
            guardedOnClick(e, e => pinClick(e))
        }, e)
    }

    const onClickOutside = () => {
        clearTimeout()
        setState('hide')
    }

    const isModifierHeld = (e: React.MouseEvent) => e.altKey || e.ctrlKey || e.shiftKey || e.metaKey

    const onPointerDown = (e: React.PointerEvent<HTMLSpanElement>) => {
        // We have special handling for some modifier+click events, so prevent default browser
        // events from interfering when a modifier is held.
        if (isModifierHeld(e)) {
            e.preventDefault()
        }
    }

    const onPointerOver = (e: React.PointerEvent<HTMLSpanElement>) => {
        if (!isModifierHeld(e)) {
            guardMouseEvent(_ => startShowTimeout(), e)
        }
    }

    const onPointerOut = (e: React.PointerEvent<HTMLSpanElement>) => {
        guardMouseEvent(_ => startHideTimeout(), e)
    }

    const tooltip = (
        <>
            {state !== 'hide' && (
                <TipChainContext.Provider value={newHTTipChainCtx}>
                    <Tooltip reference={anchor} onPointerEnter={onPointerEnter} onPointerLeave={onPointerLeave}>
                        {tooltipChildren}
                    </Tooltip>
                </TipChainContext.Provider>
            )}
        </>
    )

    return {
        state,
        onClick,
        onClickOutside,
        onPointerDown,
        onPointerOver,
        onPointerOut,
        tooltip,
    }
}

export type WithTooltipOnHoverProps = React.HTMLProps<HTMLSpanElement> & {
    tooltipChildren: React.ReactNode
}

/**
 * Span that uses the logic of {@link useHoverTooltip}.
 */
export function WithTooltipOnHover(props_: WithTooltipOnHoverProps) {
    const { tooltipChildren, ...props } = props_

    const ref = React.useRef<HTMLSpanElement>(null)

    const [logicalSpanElt, logicalDomStorage] = useLogicalDomObserver(ref)

    const ht = useHoverTooltip(ref, tooltipChildren)

    useOnClickOutside(logicalSpanElt, ht.onClickOutside, ht.state !== 'hide')

    return (
        <LogicalDomContext.Provider value={logicalDomStorage}>
            <span
                {...props}
                ref={ref}
                onClick={e => ht.onClick(e)}
                onPointerDown={e => ht.onPointerDown(e)}
                onPointerOver={e => ht.onPointerOver(e)}
                onPointerOut={e => ht.onPointerOut(e)}
            >
                {ht.tooltip}
                {props.children}
            </span>
        </LogicalDomContext.Provider>
    )
}
