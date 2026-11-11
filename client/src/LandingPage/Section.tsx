import type { ReactNode } from 'react'
import { twMerge } from 'tailwind-merge'

/** A section of the landing page  */
export function Section({
  title,
  children,
  className,
  as: Tag = 'section',
}: {
  title?: string
  children: ReactNode
  /** for the centered content */
  className?: string
  /** a `div` does not count for the alternating background */
  as?: 'section' | 'div'
}) {
  return (
    <Tag className="w-full px-4 py-10">
      <div
        className={twMerge(
          'mx-auto flex-col w-full max-w-3xl gap-3',
          className,
        )}
      >
        {title && <h2>{title}</h2>}
        {children}
      </div>
    </Tag>
  )
}
