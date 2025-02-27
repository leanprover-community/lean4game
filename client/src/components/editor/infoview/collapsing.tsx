import * as React from 'react'

/** Returns `[node, isVisible]`. Attach `node` to the dom element you care about as `<div ref={node}>...</div>` and
 * `isVisible` will change depending on whether the node is visible in the viewport or not. */
// NOTE: Unused.
export function useIsVisible(): [(element: HTMLElement) => void, boolean] {
    const [isVisible, setIsVisible] = React.useState<boolean>(false)
    const observer = React.useRef<IntersectionObserver | null>(null)
    const node = React.useCallback<(element: HTMLElement) => void>(n => {
        if (observer.current) {
            observer.current.disconnect()
        }
        if (n !== null) {
            // this is called when the given element is mounted.
            observer.current = new IntersectionObserver(
                ([x]) => {
                    setIsVisible(x.isIntersecting)
                },
                { threshold: 0, root: null, rootMargin: '0px' },
            )
            observer.current.observe(n)
        } else {
            // when unmounted
        }
    }, [])
    return [node, isVisible]
}

interface DetailsProps {
    initiallyOpen?: boolean
    children: [React.ReactNode, ...React.ReactNode[]]
    setOpenRef?: (_: React.Dispatch<React.SetStateAction<boolean>>) => void
}

/** Like `<details>` but can be programatically revealed using `setOpenRef`.
 * The first child is placed inside the `<summary>` node. */
export function Details({ initiallyOpen, children: [summary, ...children], setOpenRef }: DetailsProps): JSX.Element {
    const [isOpen, setOpen] = React.useState<boolean>(initiallyOpen === undefined ? false : initiallyOpen)
    if (setOpenRef) setOpenRef(setOpen)
    return (
        <details open={isOpen}>
            <summary
                className="mv2 pointer "
                onClick={e => {
                    if (!e.defaultPrevented) setOpen(!isOpen)
                    // See https://github.com/facebook/react/issues/15486#issuecomment-873516817
                    e.preventDefault()
                }}
            >
                {summary}
            </summary>
            {isOpen && children}
        </details>
    )
}
