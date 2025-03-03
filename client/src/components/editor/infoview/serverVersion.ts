/**
 * Keeps track of the Lean server version and available features.
 * @module
 */

export class ServerVersion {
    major: number
    minor: number
    patch: number

    constructor(version: string) {
        const vs = version.split('.')
        if (vs.length === 2) {
            this.major = parseInt(vs[0])
            this.minor = parseInt(vs[1])
            this.patch = 0
        } else if (vs.length === 3) {
            this.major = parseInt(vs[0])
            this.minor = parseInt(vs[1])
            this.patch = parseInt(vs[2])
        } else {
            throw new Error(`cannot parse Lean server version '${version}'`)
        }
    }
}
