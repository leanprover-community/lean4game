import * as React from 'react';
import { useContext } from 'react';
import ReactMarkdown from 'react-markdown';
import remarkMath from 'remark-math'
import rehypeKatex from 'rehype-katex'
import 'katex/dist/katex.min.css' // `rehype-katex` does not import the CSS for you
import gfm from "remark-gfm";
import { GameIdContext } from '../app';

export function Markdown(props: any) {
  const gameId = useContext(GameIdContext)
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
    <ReactMarkdown {...newProps} className="markdown" />
  );
}
