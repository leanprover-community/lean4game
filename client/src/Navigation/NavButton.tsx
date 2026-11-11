import type { IconDefinition } from '@fortawesome/fontawesome-svg-core'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import type { ReactNode } from 'react'
import { twMerge } from 'tailwind-merge'

import { Link } from '../components/Link'

type NavButtonProps = {
  icon?: IconDefinition
  /** shown instead of `icon` */
  iconElement?: ReactNode
  /** shown next to the icon */
  text?: string
  /** tooltip, also the accessible name if there is no `text` */
  title: string
  /** a page of the client to navigate to, or an external URL opened in a new tab */
  href?: string
  onClick?: () => void
  disabled?: boolean
  className?: string
}

/** A button in the app bar or in one of its menus */
export function NavButton({
  icon,
  iconElement,
  text,
  title,
  href,
  onClick,
  disabled = false,
  className,
}: NavButtonProps) {
  const classes = twMerge(
    'inline-flex cursor-pointer items-center gap-2 text-inherit',
    'no-underline rounded px-3 py-2 whitespace-nowrap hover:bg-white/15',
    'disabled:cursor-default disabled:opacity-50 disabled:hover:bg-transparent',
    className,
  )
  const content = (
    <>
      {iconElement ?? (icon && <FontAwesomeIcon icon={icon} />)}
      {text}
    </>
  )
  const ariaLabel = text ? undefined : title
  if (href && !disabled && /^https?:\/\//.test(href)) {
    return (
      <a
        className={classes}
        href={href}
        title={title}
        aria-label={ariaLabel}
        target="_blank"
        rel="noreferrer"
        onClick={onClick}
      >
        {content}
      </a>
    )
  }
  if (href && !disabled) {
    return (
      <Link
        className={classes}
        href={href}
        title={title}
        aria-label={ariaLabel}
        onClick={onClick}
      >
        {content}
      </Link>
    )
  }
  return (
    <button
      type="button"
      className={classes}
      title={title}
      aria-label={ariaLabel}
      disabled={disabled}
      onClick={onClick}
    >
      {content}
    </button>
  )
}
