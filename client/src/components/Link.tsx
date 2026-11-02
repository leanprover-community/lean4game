import { useSetAtom } from 'jotai'
import type { ComponentProps, MouseEvent } from 'react'

import { locationAtom } from '../state/location-atoms'

type LinkProps = ComponentProps<'a'> & { href: string }

/** A link to a page of the client, which navigates without reloading the page */
export function Link({ href, onClick, children, ...props }: LinkProps) {
  const setLocation = useSetAtom(locationAtom)

  function handleClick(event: MouseEvent<HTMLAnchorElement>) {
    onClick?.(event)
    // let the browser handle e.g. ctrl+click to open a new tab
    if (
      event.defaultPrevented ||
      event.button !== 0 ||
      event.metaKey ||
      event.ctrlKey ||
      event.shiftKey ||
      event.altKey
    ) {
      return
    }
    event.preventDefault()
    const url = new URL(href, window.location.href)
    setLocation({
      pathname: url.pathname,
      searchParams: url.searchParams,
      hash: url.hash,
    })
  }

  return (
    <a href={href} onClick={handleClick} {...props}>
      {children}
    </a>
  )
}
