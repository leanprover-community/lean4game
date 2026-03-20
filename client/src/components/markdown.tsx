import * as React from 'react';
import ReactMarkdown from 'react-markdown';
import remarkMath from 'remark-math'
import rehypeKatex from 'rehype-katex'
import 'katex/dist/katex.min.css' // `rehype-katex` does not import the CSS for you
import gfm from "remark-gfm";
import { useAtom } from 'jotai';
import { gameIdAtom } from '../store/location-atoms';

export function Markdown(props: any) {
  const [gameId] = useAtom(gameIdAtom)

  // Prefix image URLs of the form  `![...](images/...)` with the game ID
  let children = props?.children

  if (typeof children === "string") {
    children = children.replace(
      /!\[([^\]]+)\]\((images\/[^\)]+)\)/g,
      (match, text, url) => `![${text}](data/${gameId}/${url})`
    );
  }

  const newProps = {
    ...props,
    children,
    remarkPlugins: [...props.remarkPlugins ?? [], remarkMath, gfm],
    rehypePlugins: [...props.remarkPlugins ?? [], rehypeKatex],
  };
  return (
    <div className="markdown">
      <ReactMarkdown {...newProps} />
    </div>
  );
}
