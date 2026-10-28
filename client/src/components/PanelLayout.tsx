import type { IconDefinition } from '@fortawesome/fontawesome-svg-core'
import {
  faAnglesLeft,
  faAnglesRight,
  faXmark,
} from '@fortawesome/free-solid-svg-icons'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { useAtom, useAtomValue } from 'jotai'
import { type ReactNode, useEffect, useId, useRef } from 'react'
import { useTranslation } from 'react-i18next'
import {
  Group,
  Panel,
  type PanelSize,
  Separator,
  usePanelRef,
} from 'react-resizable-panels'
import { twMerge } from 'tailwind-merge'

import { leftPanelOpenAtom, rightPanelOpenAtom } from '../state/layout-atoms'
import { mobileAtom } from '../state/preferences-atoms'

type Side = 'left' | 'right'

type PanelLayoutProps = {
  left: ReactNode
  center: ReactNode
  right: ReactNode
  /** shown in the top bar of the side panels and in the tooltips of their toggles */
  leftTitle?: string
  rightTitle?: string
  /** shown in the top bar of the center, e.g. an icon */
  centerTitle?: ReactNode
}

/**
 * A center with a side panel on the left and on the right. On desktop the side panels
 * are next to the center and can be resized and collapsed, on mobile they are closed
 * and cover the whole layout when opened. The toggles are in the panels' top bars.
 */
export function PanelLayout(props: PanelLayoutProps) {
  const mobile = useAtomValue(mobileAtom)
  return mobile ? <MobileLayout {...props} /> : <DesktopLayout {...props} />
}

/** The open state of the side panel `side`, and the ids for `aria-controls` */
function useSidePanel(side: Side) {
  const [open, setOpen] = useAtom(
    side === 'left' ? leftPanelOpenAtom : rightPanelOpenAtom,
  )
  return { open, setOpen, id: `${useId()}-${side}` }
}

function DesktopLayout({
  left,
  center,
  right,
  leftTitle,
  rightTitle,
  centerTitle,
}: PanelLayoutProps) {
  const leftPanel = useSidePanel('left')
  const rightPanel = useSidePanel('right')
  return (
    <Group orientation="horizontal" className="h-full">
      <SidePanel side="left" title={leftTitle} state={leftPanel}>
        {left}
      </SidePanel>
      <PanelSeparator />
      <Panel minSize="30%" className="flex-col">
        <TopBar title={centerTitle}>
          {!leftPanel.open && (
            <OpenButton side="left" title={leftTitle} state={leftPanel} />
          )}
          {!rightPanel.open && (
            <OpenButton side="right" title={rightTitle} state={rightPanel} />
          )}
        </TopBar>
        <PanelBody>{center}</PanelBody>
      </Panel>
      <PanelSeparator />
      <SidePanel side="right" title={rightTitle} state={rightPanel}>
        {right}
      </SidePanel>
    </Group>
  )
}

/** A resizable, collapsible side panel of the desktop layout */
function SidePanel({
  side,
  title,
  state: { open, setOpen, id },
  children,
}: {
  side: Side
  title?: string
  state: ReturnType<typeof useSidePanel>
  children: ReactNode
}) {
  const panelRef = usePanelRef()
  // `expand()` would reopen the panel with its minimum size
  const lastOpenSize = useRef('25%')

  // apply the toggles to the panel
  useEffect(() => {
    const panel = panelRef.current
    if (!panel) return
    if (open && panel.isCollapsed()) panel.resize(lastOpenSize.current)
    if (!open && !panel.isCollapsed()) panel.collapse()
  }, [open, panelRef])

  // and dragging the panel closed or open to the toggles
  const onResize = ({ asPercentage }: PanelSize) => {
    const isOpen = asPercentage > 0
    if (isOpen) lastOpenSize.current = `${asPercentage}%`
    if (isOpen !== open) setOpen(isOpen)
  }

  return (
    <Panel
      id={id}
      panelRef={panelRef}
      defaultSize={open ? '25%' : '0%'}
      minSize="15%"
      collapsible
      onResize={onResize}
      className="flex-col"
    >
      <TopBar title={title}>
        <CloseButton side={side} title={title} state={{ open, setOpen, id }} />
      </TopBar>
      <PanelBody>{children}</PanelBody>
    </Panel>
  )
}

function PanelSeparator() {
  return (
    <Separator className="w-px bg-(--border) outline-none focus-visible:bg-primary data-[separator=active]:bg-primary data-[separator=hover]:bg-primary" />
  )
}

function MobileLayout({
  left,
  center,
  right,
  leftTitle,
  rightTitle,
  centerTitle,
}: PanelLayoutProps) {
  const leftPanel = useSidePanel('left')
  const rightPanel = useSidePanel('right')

  // only one side panel at a time
  const openOnly = (side: Side) => (open: boolean) => {
    leftPanel.setOpen(side === 'left' && open)
    rightPanel.setOpen(side === 'right' && open)
  }
  const leftState = { ...leftPanel, setOpen: openOnly('left') }
  const rightState = { ...rightPanel, setOpen: openOnly('right') }

  return (
    <div className="relative flex-col h-full">
      <TopBar title={centerTitle}>
        <OpenButton side="left" title={leftTitle} state={leftState} />
        <OpenButton side="right" title={rightTitle} state={rightState} />
      </TopBar>
      <PanelBody>{center}</PanelBody>
      {[
        {
          side: 'left' as const,
          title: leftTitle,
          state: leftState,
          body: left,
        },
        {
          side: 'right' as const,
          title: rightTitle,
          state: rightState,
          body: right,
        },
      ].map(
        ({ side, title, state, body }) =>
          state.open && (
            <div
              key={side}
              id={state.id}
              className="absolute inset-0 z-20 flex-col bg-(--bg)"
            >
              <TopBar title={title}>
                <CloseButton mobile side={side} title={title} state={state} />
              </TopBar>
              <PanelBody>{body}</PanelBody>
            </div>
          ),
      )}
    </div>
  )
}

/**
 * The bar at the top of a panel with its `title`. The `children` are `ToggleButton`s,
 * placed before or after the title depending on their `side`.
 */
function TopBar({
  title,
  children,
}: {
  title?: ReactNode
  children: ReactNode
}) {
  return (
    <div className="flex h-10 shrink-0 items-center gap-1 border-b border-(--border) bg-(--section-bg) px-1">
      <span className="min-w-0 flex-1 truncate px-2 font-bold">{title}</span>
      {children}
    </div>
  )
}

function PanelBody({ children }: { children: ReactNode }) {
  return <div className="min-h-0 flex-1 overflow-y-auto">{children}</div>
}

function ToggleButton({
  side,
  icon,
  label,
  state: { open, setOpen, id },
}: {
  side: Side
  icon: IconDefinition
  label: string
  state: ReturnType<typeof useSidePanel>
}) {
  return (
    <button
      type="button"
      className={twMerge(
        'flex size-8 shrink-0 cursor-pointer items-center justify-center rounded hover:bg-primary/15',
        side === 'left' ? 'order-first' : 'order-last',
      )}
      title={label}
      aria-label={label}
      aria-expanded={open}
      aria-controls={id}
      onClick={() => setOpen(!open)}
    >
      <FontAwesomeIcon icon={icon} />
    </button>
  )
}

/** Opens a side panel */
function OpenButton({
  side,
  title,
  state,
}: {
  side: Side
  title?: string
  state: ReturnType<typeof useSidePanel>
}) {
  const { t } = useTranslation()
  return (
    <ToggleButton
      side={side}
      icon={side === 'left' ? faAnglesRight : faAnglesLeft}
      label={title ? t('layout.openPanel', { title }) : ''}
      state={state}
    />
  )
}

/** Closes a side panel */
function CloseButton({
  side,
  title,
  state,
  mobile = false,
}: {
  side: Side
  title?: string
  state: ReturnType<typeof useSidePanel>
  mobile?: boolean
}) {
  const { t } = useTranslation()
  return (
    <ToggleButton
      side={side === 'left' ? 'right' : 'left'}
      icon={mobile ? faXmark : side === 'left' ? faAnglesLeft : faAnglesRight}
      label={title ? t('layout.closePanel', { title }) : ''}
      state={state}
    />
  )
}
