import * as React from 'react';
import { Link, LinkProps } from "react-router-dom";

export interface ButtonProps extends LinkProps {
  disabled?: boolean
}

export function Button(props: ButtonProps) {
  if (props.disabled) {
    return <span className="btn btn-disabled" {...props}>{props.children}</span>
  } else {
    return <Link className="btn" {...props}>{props.children}</Link>
  }
}
