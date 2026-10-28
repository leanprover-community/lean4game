import cytoscape, { type LayoutOptions, type Position } from 'cytoscape'
import klay from 'cytoscape-klay'
import { useAtomValue } from 'jotai'
import { type ReactNode, useEffect, useMemo, useRef } from 'react'
import { twMerge } from 'tailwind-merge'

import type { ApiGameData } from '../api'
import { Link } from '../components/Link'
import { gameIdAtom, gamePath } from '../state/location-atoms'
import { difficultyAtom } from '../state/progress-atoms'
import { gameInfoAtom } from '../state/query-atoms'
import { useGameTranslation } from '../utils/translation'
import {
  firstIncompleteLevelAtomFamily,
  levelCompletedAtomFamily,
  levelKey,
  worldCompletedAtom,
  worldDependenciesCompletedAtomFamily,
  worldProgressAtomFamily,
} from './world-tree-atoms'

// Settings for the world tree
cytoscape.use(klay)

const r = 16 // radius of a level
const s = 10 // global scale
const lineWidth = 10 //
const ds = 0.75 // scale the resulting svg image

const NMIN = 5 // min. worldsize
const NMAX = 16 // max. world size. Level icons start spiraling out if the world has more levels.
const NSPIRAL = 12 // world size if NMAX has been passed and need to spiral.

const MINFONT = 12

type Worlds = NonNullable<ApiGameData['worlds']>

/** The positions of the worlds, laid out top-down by klay, and their bounding box */
function computeWorldLayout(worlds: Worlds) {
  const elements: cytoscape.ElementDefinition[] = []
  for (const id in worlds.nodes) {
    elements.push({ data: { id, title: worlds.nodes[id].title } })
  }
  for (const [source, target] of worlds.edges) {
    elements.push({
      data: { id: `${source} --edge-to--> ${target}`, source, target },
    })
  }
  const cy = cytoscape({
    container: null,
    elements,
    headless: true,
    styleEnabled: false,
  })

  cy.layout({
    name: 'klay',
    klay: { direction: 'DOWN', nodePlacement: 'LINEAR_SEGMENTS' },
  } as LayoutOptions).run()

  const nodes: { [id: string]: Position } = {}
  cy.nodes().forEach(node => {
    nodes[node.id()] = { ...node.position() }
  })
  const bounds = cy.nodes().boundingBox()
  cy.destroy()
  return { nodes, bounds }
}

/** The number of levels drawn around a world, at least `NMIN` */
function useDrawnWorldSize(world: string) {
  const { data: gameInfo } = useAtomValue(gameInfoAtom)
  return Math.max(gameInfo?.worldSize?.[world] ?? NMIN, NMIN)
}

/**
 * The link to a level `level` of the world, `0` is the world's introduction. Without
 * link if `disabled`.
 */
function LevelLink({
  world,
  level,
  disabled,
  className,
  children,
}: {
  world: string
  level: number
  disabled: boolean
  className: string
  children: ReactNode
}) {
  const gameId = useAtomValue(gameIdAtom)
  if (disabled || gameId === undefined)
    return <g className={className}>{children}</g>
  return (
    <Link
      href={
        level > 0 ? gamePath(gameId, world, level) : gamePath(gameId, world)
      }
      className={twMerge(className, 'cursor-pointer no-underline')}
    >
      {children}
    </Link>
  )
}

/** svg object for a level in the game tree */
function LevelIcon({
  world,
  level,
  position,
}: {
  world: string
  level: number
  position: Position
}) {
  const difficulty = useAtomValue(difficultyAtom)
  const levelUnlocked = useAtomValue(
    levelCompletedAtomFamily(levelKey(world, level - 1)),
  )
  const worldUnlocked = useAtomValue(
    worldDependenciesCompletedAtomFamily(world),
  )
  const worldProgress = useAtomValue(worldProgressAtomFamily(world))
  const completed = useAtomValue(
    levelCompletedAtomFamily(levelKey(world, level)),
  )

  const unlocked = level <= 1 ? worldUnlocked && levelUnlocked : levelUnlocked
  const levelDisabled = difficulty >= 2 && !(unlocked || completed)

  const N = useDrawnWorldSize(world)

  // divide circle into `N+2` equal pieces.
  // only for non-spiraling case
  const beta =
    (2 * Math.PI) / Math.min(N + 2, (N < NMAX + 1 ? NMAX : NSPIRAL) + 1)

  // We want distance between two level icons to be `2.2*r`, therefore:
  // Sinus-Satz: (1.1*r) / sin(β/2) = R / sin(π/2)
  const R = (1.1 * r) / Math.sin(beta / 2)

  /** In the spiral, the angle `β` should decrease to avoid big gaps between levels.
   * This is a simplified function, which has little mathematical foundation, but
   * works fine in tests up to `N=30`.
   */
  function betaSpiral(n: number) {
    return (
      (2 * Math.PI) / (NSPIRAL + 1 + (2 * Math.max(0, n - 2)) / (NSPIRAL + 1))
    )
  }

  const x =
    N < NMAX + 1
      ? // normal case
        s * position.x + Math.sin(level * beta) * R
      : // spiraling case
        s * position.x +
        Math.sin(level * betaSpiral(level)) *
          (R + (2 * r * (level - 1)) / (NSPIRAL + 1))
  const y =
    N < NMAX + 1
      ? // normal case
        s * position.y - Math.cos(level * beta) * R
      : // spiraling case
        s * position.y -
        Math.cos(level * betaSpiral(level)) *
          (R + (2 * r * (level - 1)) / (NSPIRAL + 1))

  // Show world intro if it hasn't been read so far
  let targetLevel = level
  if (level <= 1) {
    targetLevel = worldProgress?.readIntro ? 1 : 0
  }

  return (
    <LevelLink
      world={world}
      level={targetLevel}
      disabled={levelDisabled}
      className="group"
    >
      <circle
        className={
          completed
            ? 'fill-green-600'
            : unlocked
              ? 'fill-primary'
              : 'fill-gray-300'
        }
        cx={x}
        cy={y}
        r={r}
      />
      <foreignObject
        x={x}
        y={y}
        width={1.42 * r}
        height={1.42 * r}
        transform={`translate(${-0.71 * r},${-0.71 * r})`}
        className="overflow-visible"
      >
        <div className="flex size-full items-center justify-center overflow-visible">
          <p
            className={twMerge(
              'm-0 p-0 text-center leading-none font-normal text-white',
              // shown on hover
              'opacity-0 transition-opacity duration-300 group-hover:opacity-100',
            )}
            style={{ fontSize: `${Math.floor(r)}px` }}
          >
            {level}
          </p>
        </div>
      </foreignObject>
    </LevelLink>
  )
}

/** svg object of one world in the game tree */
function WorldIcon({
  world,
  title,
  position,
}: {
  world: string
  title: string
  position: Position
}) {
  const gameId = useAtomValue(gameIdAtom)
  const { data: gameInfo } = useAtomValue(gameInfoAtom)
  const { t: gameT } = useGameTranslation(
    gameId ?? '',
    gameInfo?.settings?.allowEmptyTranslations,
  )
  const difficulty = useAtomValue(difficultyAtom)
  const unlocked = useAtomValue(worldDependenciesCompletedAtomFamily(world))
  const completed = useAtomValue(worldCompletedAtom(world))
  const worldDisabled = difficulty >= 2 && !(unlocked || completed)
  const firstUncompleted = useAtomValue(firstIncompleteLevelAtomFamily(world))

  // See level icons. Match radius computed there minus `1.2*r`
  const N = useDrawnWorldSize(world)
  const betaHalf =
    Math.PI / Math.min(N + 2, (N < NMAX + 1 ? NMAX : NSPIRAL) + 1)
  const R = (1.1 * r) / Math.sin(betaHalf) - 1.2 * r

  // Offset for the labels for small worlds
  const labelOffset = R + 2.5 * r

  return (
    <LevelLink
      world={world}
      level={firstUncompleted}
      disabled={worldDisabled}
      className=""
    >
      <circle
        cx={s * position.x}
        cy={s * position.y}
        r={R}
        className={
          completed
            ? 'fill-green-700'
            : unlocked
              ? 'fill-primary'
              : 'fill-gray-400'
        }
      />
      <foreignObject
        x={s * position.x - 75}
        y={s * position.y + labelOffset}
        width="150px"
        height="2em"
        className="overflow-visible"
      >
        <div
          // the old client scrolled the tree to the world which can be played next
          data-playable={unlocked && !completed ? true : undefined}
          className={twMerge(
            'rounded-lg p-0.5',
            completed
              ? 'bg-green-800'
              : unlocked
                ? 'bg-primary'
                : 'bg-gray-500',
          )}
        >
          <p
            className="m-0 p-0 text-center leading-normal font-bold text-white"
            style={{ fontSize: `${MINFONT}px` }}
          >
            {title ? gameT(title) : world}
          </p>
        </div>
      </foreignObject>
    </LevelLink>
  )
}

/** svg object for a connection path between worlds in the game tree */
function WorldPath({
  source,
  target,
  sourceWorld,
}: {
  source: Position
  target: Position
  sourceWorld: string
}) {
  const sourceCompleted = useAtomValue(worldCompletedAtom(sourceWorld))
  return (
    <line
      x1={s * source.x}
      y1={s * source.y}
      x2={s * target.x}
      y2={s * target.y}
      className={sourceCompleted ? 'stroke-green-700' : 'stroke-gray-400'}
      strokeWidth={lineWidth}
    />
  )
}

/** The worlds of the game as a tree, with their levels around them */
export function WorldTree() {
  const gameId = useAtomValue(gameIdAtom)
  const { data: gameInfo } = useAtomValue(gameInfoAtom)
  const treeRef = useRef<HTMLDivElement>(null)

  const worlds = gameInfo?.worlds
  const worldSize = gameInfo?.worldSize

  const layout = useMemo(
    () => (worlds ? computeWorldLayout(worlds) : undefined),
    [worlds],
  )

  // scroll to the world which can be played next
  useEffect(() => {
    if (!layout) return
    treeRef.current
      ?.querySelector('[data-playable]')
      ?.scrollIntoView({ block: 'center', inline: 'center' })
  }, [layout])

  if (!worlds || !worldSize || !layout) return null
  const { nodes, bounds } = layout

  // See `LevelIcon` for calculation of the radius. Use the max. radius for calculating the padding
  const R = (1.1 * r) / Math.sin(Math.PI / (NMAX + 1))
  const padding = R + 2.1 * r

  const dx = s * (bounds.x2 - bounds.x1) + 2 * padding
  const dy = s * (bounds.y2 - bounds.y1) + 2 * padding

  return (
    <div ref={treeRef} className="h-full overflow-auto">
      <svg
        xmlns="http://www.w3.org/2000/svg"
        width={ds * dx}
        viewBox={`${s * bounds.x1 - padding} ${s * bounds.y1 - padding} ${dx} ${dy}`}
        // the labels are text, but should behave like the rest of the drawing
        className="m-auto block max-w-none cursor-default select-none"
      >
        {/* draw all connecting paths */}
        {worlds.edges.map(([source, target]) => (
          <WorldPath
            key={`path_${source}-->${target}`}
            sourceWorld={source}
            source={nodes[source]}
            target={nodes[target]}
          />
        ))}
        {/* draw the worlds and levels */}
        {Object.entries(nodes).map(([worldId, position]) => (
          <g key={`${gameId}-${worldId}`}>
            <WorldIcon
              world={worldId}
              title={worlds.nodes[worldId].title || worldId}
              position={position}
            />
            {Array.from({ length: worldSize[worldId] ?? 0 }, (_, i) => (
              <LevelIcon
                key={i + 1}
                world={worldId}
                level={i + 1}
                position={position}
              />
            ))}
          </g>
        ))}
      </svg>
    </div>
  )
}
