import * as React from 'react';
import { RefObject } from 'react';
import { Link, LinkProps } from "react-router-dom";

export interface ButtonProps extends LinkProps {
  disabled?: boolean
  inverted?: string // Apparently "inverted" in DOM cannot be `boolean` but must be `inverted`
}

const Button = React.forwardRef<HTMLAnchorElement, ButtonProps>((props, ref) => {
  if (props.disabled) {
    return <span ref={ref} className={`btn btn-disabled ${props.inverted === "true" ? 'btn-inverted' : ''}`} {...props}>{props.children}</span>
  } else {
    return <Link ref={ref} className={`btn ${props.inverted === "true" ? 'btn-inverted' : ''}`} {...props}>{props.children}</Link>
  }
})
export { Button }
