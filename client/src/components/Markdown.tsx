import 'katex/dist/katex.min.css'
import ReactMarkdown, { defaultUrlTransform } from 'react-markdown'
import rehypeKatex from 'rehype-katex'
import remarkGfm from 'remark-gfm'
import remarkMath from 'remark-math'
import { twMerge } from 'tailwind-merge'

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
        '[&>:first-child]:mt-0',
        // lists
        '[&_ol]:mx-6 [&_ol]:mb-6 [&_ol]:list-decimal',
        '[&_ul]:mx-6 [&_ul]:mb-6 [&_ul]:list-disc',
        '[&_li_ol]:mx-6 [&_li_ol]:mb-0 [&_li_ul]:mx-6 [&_li_ul]:mb-0',
      )}
    >
      <ReactMarkdown
        remarkPlugins={[remarkGfm, remarkMath]}
        rehypePlugins={[rehypeKatex]}
        urlTransform={url =>
          game && url.startsWith('images/')
            ? `/api/data/${game}/${url}`
            : defaultUrlTransform(url)
        }
      >
        {children}
      </ReactMarkdown>
    </div>
  )
}
