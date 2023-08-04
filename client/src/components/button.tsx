import * as React from 'react';
import { Link, LinkProps } from "react-router-dom";

export interface ButtonProps extends LinkProps {
  disabled?: boolean
  inverted?: string // Apparently "inverted" in DOM cannot be `boolean` but must be `inverted`
}

export function Button(props: ButtonProps) {
  if (props.disabled) {
    return <span className={`btn btn-disabled ${props.inverted === "true" ? 'btn-inverted' : ''}`} {...props}>{props.children}</span>
  } else {
    return <Link className={`btn ${props.inverted === "true" ? 'btn-inverted' : ''}`} {...props}>{props.children}</Link>
  }
}
