import { Suspense, use } from 'react'
import ReactMarkdown, { defaultUrlTransform } from 'react-markdown'
import remarkGfm from 'remark-gfm'
import remarkMath from 'remark-math'
import { twMerge } from 'tailwind-merge'

import { Spinner } from './Spinner'

type RehypeKatex = typeof import('rehype-katex').default

let rehypeKatexPromise: Promise<RehypeKatex> | undefined

/**
 * Loads `rehype-katex` and the KaTeX styles, only once. They are lazy loaded, so that
 * KaTeX is not part of the index bundle and only loaded once a text contains math.
 */
function loadRehypeKatex(): Promise<RehypeKatex> {
  rehypeKatexPromise ??= Promise.all([
    import('rehype-katex'),
    import('katex/dist/katex.min.css'),
  ]).then(([module]) => module.default)
  return rehypeKatexPromise
}

/**
 * Renders Markdown with GitHub extensions and `$…$` math. For texts of a game, pass its
 * `owner/repo` as `game`, so that images like `images/cover.png` load from the game.
 */
export function Markdown({
  children,
  game,
}: {
  children: string
  game?: string
}) {
  return (
    <div
      className={twMerge(
        // inline code and code blocks
        '[&_code]:rounded-sm [&_code]:bg-slate-200 [&_code]:px-1 [&_code]:text-sm',
        '[&_code]:text-slate-800',
        'dark:[&_code]:bg-slate-800 dark:[&_code]:text-slate-200',
        '[&_pre]:overflow-auto [&_pre]:rounded-sm [&_pre]:bg-slate-200 [&_pre]:py-2.5',
        '[&_pre]:pl-1 [&_pre]:leading-normal [&_pre]:text-slate-800',
        'dark:[&_pre]:bg-slate-800 dark:[&_pre]:text-slate-200 [&_pre_code]:p-0',
        // headings, only moderately larger than the text (overrides the global `h1`)
        '[&_h1]:mt-4 [&_h1]:mb-2 [&_h1]:text-[1.4em] [&_h1]:leading-tight',
        '[&_h2]:mt-3 [&_h2]:mb-2 [&_h2]:text-[1.25em] [&_h2]:leading-tight',
        '[&_h3]:mt-3 [&_h3]:mb-1 [&_h3]:text-[1.1em] [&_h3]:font-semibold',
        '[&_h4]:mt-2 [&_h4]:mb-1 [&_h4]:font-semibold',
        '[&_h5]:mt-2 [&_h5]:mb-1 [&_h5]:font-semibold',
        '[&_h6]:mt-2 [&_h6]:mb-1 [&_h6]:font-semibold',
        '*:first:mt-0',
        // lists
        '[&_ol]:mx-6 [&_ol]:mb-6 [&_ol]:list-decimal',
        '[&_ul]:mx-6 [&_ul]:mb-6 [&_ul]:list-disc',
        '[&_li_ol]:mx-6 [&_li_ol]:mb-0 [&_li_ul]:mx-6 [&_li_ul]:mb-0',
      )}
    >
      {/* `remark-math` only finds math between `$`, so other texts don't need KaTeX */}
      {children.includes('$') ? (
        <Suspense fallback={<Spinner />}>
          <MathMarkdown game={game}>{children}</MathMarkdown>
        </Suspense>
      ) : (
        <MarkdownContent game={game}>{children}</MarkdownContent>
      )}
    </div>
  )
}

/** `MarkdownContent` with math rendered by KaTeX, suspends while KaTeX is loading */
function MathMarkdown({ children, game }: { children: string; game?: string }) {
  const rehypeKatex = use(loadRehypeKatex())
  return (
    <MarkdownContent game={game} rehypeKatex={rehypeKatex}>
      {children}
    </MarkdownContent>
  )
}

/** The rendered Markdown, with math rendered by `rehypeKatex` if it is given */
function MarkdownContent({
  children,
  game,
  rehypeKatex,
}: {
  children: string
  game?: string
  rehypeKatex?: RehypeKatex
}) {
  return (
    <ReactMarkdown
      remarkPlugins={[remarkGfm, remarkMath]}
      rehypePlugins={rehypeKatex ? [rehypeKatex] : []}
      urlTransform={url =>
        game && url.startsWith('images/')
          ? `/api/data/${game}/${url}`
          : defaultUrlTransform(url)
      }
    >
      {children}
    </ReactMarkdown>
  )
}
