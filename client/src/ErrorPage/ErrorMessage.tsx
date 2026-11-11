import type { ReactNode } from 'react'
import { twMerge } from 'tailwind-merge'

/** Sizes and positions of the bubbles leading from the robot to the message */
const thoughtBubbles = [
  'left-4 -bottom-14 size-9.5',
  'left-10 -bottom-24 size-8',
  'left-18 -bottom-30 size-6.5',
  'left-27 -bottom-33 size-5.5',
]

/**
 * A full page showing `children` in a thought bubble with a surprised robot below it.
 * The robot fills the remaining height and only overlaps with the small bubbles.
 */
export function ErrorMessage({ children }: { children: ReactNode }) {
  return (
    <div className="flex-col h-full items-center">
      <div
        className={twMerge(
          'relative m-8 flex-col max-h-1/3 max-w-160 rounded-2xl border-2',
          'border-error bg-error-bg text-gray-900',
        )}
      >
        <div className="min-h-0 overflow-y-auto p-4">{children}</div>
        {thoughtBubbles.map(classes => (
          <div
            key={classes}
            className={twMerge(
              'absolute rounded-full border-2 border-error bg-error-bg',
              classes,
            )}
          />
        ))}
      </div>
      <img
        src="/RoboSurprised.png"
        alt=""
        className="min-h-0 flex-1 object-contain"
      />
    </div>
  )
}

/** Link to the issues of the lean4game repo, the text is passed by `<Trans>` */
export function IssueLink({ children }: { children?: ReactNode }) {
  return (
    <a
      href="https://github.com/leanprover-community/lean4game/issues"
      target="_blank"
      rel="noreferrer"
    >
      {children}
    </a>
  )
}
