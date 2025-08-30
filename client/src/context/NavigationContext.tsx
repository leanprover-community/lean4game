import * as React from 'react'
import { createContext } from 'react'

/** Context which manages the dropdown navigation */
export const NavigationContext = createContext<{
  navOpen: boolean,
  setNavOpen: React.Dispatch<React.SetStateAction<boolean>>
}>({navOpen: false, setNavOpen: () => {}})
