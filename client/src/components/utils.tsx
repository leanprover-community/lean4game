import * as React from 'react'
import { Link, LinkProps } from "react-router-dom"
import { Box, CircularProgress } from "@mui/material"
import ReactMarkdown from 'react-markdown'
import remarkMath from 'remark-math'
import rehypeKatex from 'rehype-katex'
import rehypeRaw from 'rehype-raw'
import 'katex/dist/katex.min.css' // `rehype-katex` does not import the CSS for you
import gfm from "remark-gfm"

/** Simple loading icon */
export function LoadingIcon () {
  return <Box display="flex" alignItems="center" justifyContent="center" sx={{ flex: 1, height: "calc(100vh - 64px)" }}>
    <CircularProgress />
  </Box>
}

export interface ButtonProps extends LinkProps {
  disabled?: boolean
  inverted?: string // Apparently "inverted" in DOM cannot be `boolean` but must be `inverted`
}


/** Our own button class */
export function Button(props: ButtonProps) {
  if (props.disabled) {
    return <span className={`btn btn-disabled ${props.inverted === "true" ? 'btn-inverted' : ''}`} {...props}>{props.children}</span>
  } else {
    return <Link className={`btn ${props.inverted === "true" ? 'btn-inverted' : ''}`} {...props}>{props.children}</Link>
  }
}

/** Spiced-up markdown */
export function Markdown(props) {
  const newProps = {
      ...props,
      remarkPlugins: [...props.remarkPlugins ?? [], remarkMath, gfm],
      rehypePlugins: [...props.remarkPlugins ?? [], rehypeKatex, rehypeRaw],
    };
    return (
      <ReactMarkdown {...newProps} className="markdown" />
    );
}
