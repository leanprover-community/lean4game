import type { ButtonHTMLAttributes, ComponentProps } from 'react'
import { twMerge } from 'tailwind-merge'

import { Link } from './Link'

const buttonClass = twMerge(
  'cursor-pointer rounded bg-primary px-3 py-1.5 text-white hover:bg-primary/85',
  'disabled:cursor-default disabled:opacity-50 disabled:hover:bg-primary',
)

/** A button with the primary colour, e.g. in popups */
export function Button({
  className,
  type = 'button',
  ...props
}: ButtonHTMLAttributes<HTMLButtonElement>) {
  return (
    <button
      type={type}
      className={twMerge(buttonClass, className)}
      {...props}
    />
  )
}

/** A link to a page of the client, looking like a `Button` */
export function LinkButton({
  className,
  ...props
}: ComponentProps<typeof Link>) {
  return (
    <Link
      className={twMerge(buttonClass, 'no-underline', className)}
      {...props}
    />
  )
}
