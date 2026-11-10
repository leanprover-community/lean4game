import {
  createContext,
  Fragment,
  type ReactNode,
  type RefObject,
  useContext,
  useEffect,
  useRef,
  useState,
} from 'react'
import { createPortal } from 'react-dom'
import { twMerge } from 'tailwind-merge'

import type { ApiCode, ApiHover } from '../../api'
import { Markdown } from '../../components/Markdown'

type HoverInfo = { hovers: ApiHover[]; hoverDocs: string[] }

const HoverContext = createContext<{
  info: HoverInfo
  /** shows the hover `index` at `target`, `null` hides it after a short delay */
  show: (target: HTMLElement | null, index?: number) => void
} | null>(null)

/** Shows the hover information of the `HoverCode`s inside, see `ApiProofCheckResult` */
export function HoverProvider({
  hovers,
  hoverDocs,
  children,
}: HoverInfo & { children: ReactNode }) {
  const [active, setActive] = useState<{
    target: HTMLElement
    index: number
  } | null>(null)
  const hideTimeout = useRef<ReturnType<typeof setTimeout>>(undefined)
  const popupRef = useRef<HTMLDivElement>(null)

  const show = (target: HTMLElement | null, index?: number) => {
    clearTimeout(hideTimeout.current)
    if (target && index !== undefined) setActive({ target, index })
    else hideTimeout.current = setTimeout(() => setActive(null), 150)
  }
  useEffect(() => () => clearTimeout(hideTimeout.current), [])

  // the tooltip is positioned at the expression, so it would stay behind on scrolling,
  // except when scrolling the tooltip itself
  useEffect(() => {
    if (!active) return
    const hide = (ev: Event) => {
      if (ev.target instanceof Node && popupRef.current?.contains(ev.target))
        return
      setActive(null)
    }
    window.addEventListener('scroll', hide, true)
    return () => window.removeEventListener('scroll', hide, true)
  }, [active])

  return (
    <HoverContext.Provider value={{ info: { hovers, hoverDocs }, show }}>
      {children}
      {active &&
        createPortal(
          <HoverPopup
            ref={popupRef}
            target={active.target}
            hover={hovers[active.index]}
            doc={hoverDocs[hovers[active.index]?.doc ?? -1]}
            // keep it open while the mouse is on it, e.g. to select text
            onMouseEnter={() => clearTimeout(hideTimeout.current)}
            onMouseLeave={() => show(null)}
          />,
          document.body,
        )}
    </HoverContext.Provider>
  )
}

/** The tooltip below (or above) the hovered expression */
function HoverPopup({
  ref,
  target,
  hover,
  doc,
  onMouseEnter,
  onMouseLeave,
}: {
  ref: RefObject<HTMLDivElement | null>
  target: HTMLElement
  hover?: ApiHover
  doc?: string
  onMouseEnter: () => void
  onMouseLeave: () => void
}) {
  if (!hover || !(hover.expr || hover.type || doc)) return null
  const rect = target.getBoundingClientRect()
  const below = rect.bottom < window.innerHeight / 2
  return (
    <div
      ref={ref}
      role="tooltip"
      // scrolling to its end must not scroll the proof, which would close the tooltip
      className={twMerge(
        // at most 36rem, and smaller on small screens
        'fixed z-50 max-h-[40svh] max-w-[min(36rem,90svw)]',
        'overflow-auto overscroll-contain rounded border border-(--border)',
        'bg-(--bg) px-3 py-2 text-sm text-(--text-h) shadow-(--shadow)',
      )}
      style={{
        left: Math.max(8, Math.min(rect.left, window.innerWidth - 300)),
        ...(below
          ? { top: rect.bottom + 4 }
          : { bottom: window.innerHeight - rect.top + 4 }),
      }}
      onMouseEnter={onMouseEnter}
      onMouseLeave={onMouseLeave}
    >
      {(hover.expr || hover.type) && (
        <div className="font-mono whitespace-pre-wrap">
          {hover.expr}
          {hover.expr && hover.type && ' : '}
          {hover.type}
        </div>
      )}
      {doc && (
        <div className="mt-2 border-t border-(--border) pt-2">
          <Markdown>{doc}</Markdown>
        </div>
      )}
    </div>
  )
}

/** Lean code where the subexpressions show their type and documentation on hover */
export function HoverCode({
  code,
  fallback,
}: {
  code?: ApiCode
  fallback: string
}) {
  if (!code) return <LeanText text={fallback} />
  return <CodePart code={code} />
}

/** Text with the `✝` of inaccessible names like `x✝` as a small superscript */
export function LeanText({ text }: { text: string }) {
  if (!text.includes('✝')) return text
  return text.split('✝').map((part, i) => (
    <Fragment key={i}>
      {i > 0 && <sup className="text-xs">✝</sup>}
      {part}
    </Fragment>
  ))
}

function CodePart({ code }: { code: ApiCode }) {
  if ('text' in code) return <LeanText text={code.text} />
  if ('append' in code)
    return code.append.map((c, i) => <CodePart key={i} code={c} />)
  return <HoverTag index={code.tag[0]} code={code.tag[1]} />
}

/** A subexpression with hover information, only the innermost hovered one is highlighted */
function HoverTag({ index, code }: { index: number; code: ApiCode }) {
  const context = useContext(HoverContext)
  const [hovered, setHovered] = useState(false)
  if (!context) return <CodePart code={code} />
  return (
    <span
      className={hovered ? 'rounded-sm bg-primary/20' : undefined}
      onMouseOver={ev => {
        ev.stopPropagation()
        setHovered(true)
        context.show(ev.currentTarget, index)
      }}
      onMouseOut={ev => {
        ev.stopPropagation()
        setHovered(false)
        context.show(null)
      }}
    >
      <CodePart code={code} />
    </span>
  )
}
