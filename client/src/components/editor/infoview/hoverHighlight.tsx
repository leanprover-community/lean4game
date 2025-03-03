import React from 'react'
import { HoverState } from './tooltips'

export interface HoverHighlightSettings {
    ref: React.RefObject<HTMLSpanElement>
    /**
     * Whether to return the `highlight` CSS class on hover.
     */
    highlightOnHover: boolean
    /**
     * Whether to return the `underline` CSS class on hover while holding `Ctrl` / `Meta`.
     */
    underlineOnModHover: boolean
}

export interface HoverHighlight {
    hoverState: HoverState
    setHoverState: React.Dispatch<React.SetStateAction<HoverState>>
    className: string
    onPointerOver: (e: React.PointerEvent<HTMLSpanElement>) => void
    onPointerOut: (e: React.PointerEvent<HTMLSpanElement>) => void
    onPointerMove: (e: React.PointerEvent<HTMLSpanElement>) => void
}

/**
 * Logic for a component that is highlighted/underlined when hovered over.
 * The component is passed in `settings.ref`.
 *
 * The hook returns the current hover state of the component,
 * a string of CSS classes containing `highlight` and/or `underline` when appropriate,
 * as well as event handlers which the the caller must attach to the component.
 */
export function useHoverHighlight(settings: HoverHighlightSettings): HoverHighlight {
    const { ref, highlightOnHover, underlineOnModHover } = settings

    const [hoverState, setHoverState] = React.useState<HoverState>('off')
    const isHoveredOver = hoverState !== 'off'

    let className: string = ''
    if (highlightOnHover && isHoveredOver) {
        className += 'highlight '
    }
    if (underlineOnModHover && hoverState === 'ctrlOver') {
        className += 'underline '
    }

    const onPointerEvent = (b: boolean, e: React.PointerEvent<HTMLSpanElement>) => {
        // It's more composable to let pointer events bubble up rather than to call `stopPropagation`,
        // but we only want to handle hovers in the innermost component. So we record that the
        // event was handled with a property.
        // The `contains` check ensures that the node hovered over is a child in the DOM
        // tree and not just a logical React child (see useLogicalDom and
        // https://reactjs.org/docs/portals.html#event-bubbling-through-portals).
        if (ref.current && e.target instanceof Node && ref.current.contains(e.target)) {
            if ('_DetectHoverSpanSeen' in e) {
                return
            }
            ;(e as any)._DetectHoverSpanSeen = {}
            if (!b) {
                setHoverState('off')
            } else if (e.ctrlKey || e.metaKey) {
                setHoverState('ctrlOver')
            } else {
                setHoverState('over')
            }
        }
    }
    const onPointerOver = (e: React.PointerEvent<HTMLSpanElement>) => onPointerEvent(true, e)
    const onPointerOut = (e: React.PointerEvent<HTMLSpanElement>) => onPointerEvent(false, e)

    const onPointerMove = (e: React.PointerEvent<HTMLSpanElement>) => {
        if (e.ctrlKey || e.metaKey) {
            setHoverState(st => (st === 'over' ? 'ctrlOver' : st))
        } else {
            setHoverState(st => (st === 'ctrlOver' ? 'over' : st))
        }
    }

    const onKeyDown = React.useCallback((e: KeyboardEvent) => {
        if (e.key === 'Control' || e.key === 'Meta') {
            setHoverState(st => (st === 'over' ? 'ctrlOver' : st))
        }
    }, [])

    const onKeyUp = React.useCallback((e: KeyboardEvent) => {
        if (e.key === 'Control' || e.key === 'Meta') {
            setHoverState(st => (st === 'ctrlOver' ? 'over' : st))
        }
    }, [])

    React.useEffect(() => {
        if (!isHoveredOver) {
            // Avoid adding lots of expensive global event handlers for spans that are not being
            // hovered over
            return
        }

        // These event handlers do not fire when the InfoView is not focused.
        document.addEventListener('keydown', onKeyDown)
        document.addEventListener('keyup', onKeyUp)

        return () => {
            document.removeEventListener('keydown', onKeyDown)
            document.removeEventListener('keyup', onKeyUp)
        }
    }, [onKeyDown, onKeyUp, isHoveredOver])

    return {
        hoverState,
        setHoverState,
        className,
        onPointerOver,
        onPointerOut,
        onPointerMove,
    }
}
