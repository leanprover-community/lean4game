import * as React from 'react';

export interface ButtonProps
  extends React.ButtonHTMLAttributes<HTMLButtonElement> {
  inverted?: boolean
}

export const Button = React.forwardRef<HTMLButtonElement, ButtonProps>(
  ({ disabled, inverted, children, onClick, ...rest }, ref) => {
    return <button
      ref={ref}
      className={`btn ${disabled ? 'btn-disabled' : ''} ${inverted ? 'btn-inverted' : ''}`}
      disabled={disabled}
      onClick={(ev) => {if (!disabled) onClick?.(ev)}}
      {...rest}>
        {children}
    </button>
})
