import * as React from 'react';
import ReactMarkdown from 'react-markdown';
import remarkMath from 'remark-math'
import rehypeKatex from 'rehype-katex'
import 'katex/dist/katex.min.css' // `rehype-katex` does not import the CSS for you
import gfm from "remark-gfm";

function Markdown(props) {
    const newProps = {
        ...props,
        remarkPlugins: [...props.remarkPlugins ?? [], remarkMath, gfm],
        rehypePlugins: [...props.remarkPlugins ?? [], rehypeKatex],
      };
      return (
        <ReactMarkdown {...newProps} className="markdown" />
      );
}

export default Markdown
