import * as React from 'react'
import { IconDefinition } from "@fortawesome/free-solid-svg-icons"
import { FontAwesomeIcon } from "@fortawesome/react-fontawesome"

/** A button to appear in the navigation (both, top bar or dropdown). */
export const NavButton: React.FC<{
  icon?: IconDefinition
  iconElement?: JSX.Element
  text?: string
  onClick?: React.MouseEventHandler<HTMLAnchorElement>
  title?: string
  href?: string
  inverted?: boolean
  disabled?: boolean
  className?: string
}> = ({icon, iconElement, text, onClick=()=>{}, title, href=null, inverted=false, disabled=false, className=''}) => {
  return <a className={`${className} nav-button btn${inverted?' btn-inverted':''}${disabled?' btn-disabled':''}`} onClick={disabled?null:onClick} href={disabled?null:href} title={title}>
    {iconElement ?? (icon && <FontAwesomeIcon icon={icon} />)}{text && <>&nbsp;{text}</>}
  </a>
}
