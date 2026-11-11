import fs from 'node:fs/promises'

import type { Response } from 'express'

export async function sendJsonFile(
  res: Response,
  filePath: string | undefined,
) {
  if (!filePath) {
    res.status(404).json({ error: 'Not found' })
    return
  }
  try {
    const content = await fs.readFile(filePath, 'utf-8')
    res.type('application/json').send(content)
  } catch (error) {
    if ((error as NodeJS.ErrnoException).code === 'ENOENT') {
      res.status(404).json({ error: 'Not found' })
    } else {
      res.status(500).json({
        error: `Failed to read data file: ${(error as Error).message}`,
      })
    }
  }
}
