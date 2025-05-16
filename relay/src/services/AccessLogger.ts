import http from 'http'
import { v4 as uuidv4 } from 'uuid'
import { Request, response, Response} from 'express'

export interface Connection {
  id: string,
  req: Request,
  url: string,
  startTime: Date
}

export class AccessLogger {
  private connections: Map<string, Connection> = new Map()

  logConnections(req: Request, res: Response): string {
    const id = uuidv4()
    const url: string = req.originalUrl || req.url
    const startTime: Date = new Date()

    this.connections.set(id, {id, req, url, startTime})

    res.on('close', () => {this.deleteConnection(id)})

    return id
  }

  deleteConnection(id: string): void {
    this.connections.delete(id)
  }

  getActiveConnections(): Connection[] {
    return Array.from(this.connections.values())
  }
}
