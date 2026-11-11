import { faCheck, faTerminal } from '@fortawesome/free-solid-svg-icons'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { useAtom, useAtomValue } from 'jotai'
import { useEffect, useRef, useState, type JSX } from 'react'
import { useTranslation } from 'react-i18next'
import { twMerge } from 'tailwind-merge'

import { Dropdown } from '../Navigation/Dropdown'
import { NavButton } from '../Navigation/NavButton'
import { Mask, maskAtom, masks } from './mask-atoms'
import { Raw } from './Raw/Raw'
import { Typewriter } from './Typewriter/Typewriter'

/** The selected mask, see `maskAtom` */
export function SelectedMask(): JSX.Element {
  const mask = useAtomValue(maskAtom)
  switch (mask) {
    case Mask.Raw:
      return <Raw />
    case Mask.Typewriter:
      return <Typewriter />
  }
}

/** A button with a dropdown to select the mask, for the top bar of the center */
export function MaskMenu() {
  const { t } = useTranslation()
  const [mask, setMask] = useAtom(maskAtom)
  const [open, setOpen] = useState(false)
  const ref = useRef<HTMLDivElement>(null)

  // close when clicking anywhere else
  useEffect(() => {
    if (!open) return
    const onPointerDown = (event: PointerEvent) => {
      if (!ref.current?.contains(event.target as Node)) setOpen(false)
    }
    document.addEventListener('pointerdown', onPointerDown)
    return () => document.removeEventListener('pointerdown', onPointerDown)
  }, [open])

  const label = t('masks.select')
  return (
    <div ref={ref} className="relative shrink-0">
      <button
        type="button"
        className={twMerge(
          'flex h-8 cursor-pointer items-center justify-center rounded px-2',
          'hover:bg-primary/15',
        )}
        title={label}
        aria-label={label}
        aria-haspopup="menu"
        aria-expanded={open}
        onClick={() => setOpen(!open)}
      >
        <FontAwesomeIcon icon={faTerminal} />
      </button>
      <Dropdown
        open={open}
        onClose={() => setOpen(false)}
        className="right-auto left-0 rounded-br-lg rounded-bl-none"
      >
        {masks.map(option => (
          <NavButton
            key={option}
            className="text-white"
            iconElement={
              <FontAwesomeIcon
                icon={faCheck}
                className={option === mask ? '' : 'invisible'}
              />
            }
            text={t('masks.name', { context: option })}
            title={t('masks.name', { context: option })}
            onClick={() => setMask(option)}
          />
        ))}
      </Dropdown>
    </div>
  )
}
