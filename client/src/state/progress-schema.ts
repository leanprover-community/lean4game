import { z } from 'zod'

import {
  DEFAULT_DIFFICULTY,
  type GameProgress,
  type WorldProgress,
} from './progress-types'

/*
The schema of the progress of a game, to validate uploaded files. It is lenient where
older versions of the game wrote less: missing lists and flags get their defaults.
*/

const selectionSchema = z.object({
  selectionStartLineNumber: z.number(),
  selectionStartColumn: z.number(),
  positionLineNumber: z.number(),
  positionColumn: z.number(),
})

/**
 * The steps of a proof which older versions stored as `code`: one step per line, where
 * lines indented more than the first step continue the step before them, e.g. the proof
 * of `have h : P := by`. The indentation of the first step is removed.
 */
export function proofOfCode(code: string): string[] {
  const indentation = (line: string) => line.length - line.trimStart().length
  const lines = code.split('\n').filter(line => line.trim().length > 0)
  if (lines.length === 0) return []
  const base = indentation(lines[0])
  const proof: string[] = []
  for (const line of lines) {
    const indent = indentation(line)
    const text = line.slice(Math.min(indent, base)).trimEnd()
    if (indent > base && proof.length > 0)
      proof[proof.length - 1] += '\n' + text
    else proof.push(text)
  }
  return proof
}

/** The progress of a level, older versions stored `code` instead of `proof` */
const levelProgressSchema = z
  .object({
    proof: z.array(z.string()).optional(),
    code: z.string().optional(),
    selections: z.array(selectionSchema).default([]),
    completed: z.boolean().default(false),
    help: z.array(z.number()).default([]),
  })
  .refine(level => level.proof !== undefined || level.code !== undefined, {
    message: 'Invalid input: expected array, received undefined',
    path: ['proof'],
  })
  .transform(({ proof, code, ...level }) => ({
    ...level,
    proof: proof ?? proofOfCode(code ?? ''),
  }))

/** `readIntro`, and the progress of the levels by their number */
const worldProgressSchema = z
  .object({ readIntro: z.boolean().default(false) })
  .catchall(levelProgressSchema)
  .superRefine((world, ctx) => {
    for (const key of Object.keys(world)) {
      if (key !== 'readIntro' && !/^\d+$/.test(key)) {
        ctx.addIssue({
          code: 'custom',
          path: [key],
          message: 'Expected a level number',
        })
      }
    }
  })
  .transform(world => world as WorldProgress)

export const gameProgressSchema = z.object({
  inventory: z.array(z.string()).default([]),
  difficulty: z.int().min(0).max(2).default(DEFAULT_DIFFICULTY),
  readIntro: z.boolean().default(false),
  data: z.record(z.string(), worldProgressSchema),
  typewriterMode: z.boolean().optional(),
}) satisfies z.ZodType<GameProgress>

/**
 * The progress in the JSON `text`, or a description of what is wrong with it, e.g.
 * `data.Addition.1.proof: Invalid input: expected array, received undefined`
 */
export function parseGameProgress(
  text: string,
): { progress: GameProgress } | { error: string } {
  let json: unknown
  try {
    json = JSON.parse(text)
  } catch (error) {
    return { error: (error as Error).message }
  }
  const result = gameProgressSchema.safeParse(json)
  if (result.success) return { progress: result.data }
  const issue = result.error.issues[0]
  const path = issue.path.join('.')
  return { error: path ? `${path}: ${issue.message}` : issue.message }
}
