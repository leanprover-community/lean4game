/*
This file contains integration tests for the API endpoints without
using the frontend.
*/

const uuidRegex =
  /^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/i

/** The plain text of tagged code. */
function flatten(code) {
  if ('text' in code) return code.text
  if ('append' in code) return code.append.map(flatten).join('')
  return flatten(code.tag[1])
}

describe('Data', () => {
  it('can list featured games', () => {
    cy.request('GET', '/api/games').then(res => {
      expect(res.status).to.eq(200)
      expect(res.body).to.be.an('array')
      for (const game of res.body) {
        expect(game).to.have.all.keys(
          'owner',
          'repo',
          'featured',
          'tile',
          'settings',
        )
      }
    })
  })
  it('can get game info', () => {
    cy.request('GET', '/api/data/test/testgame/game')
      .then(res => {
        expect(res.status).to.eq(200)
        return res.body
      })
      .then(data => {
        expect(data.title).to.eq('Game Skeleton')
        expect(data.worlds.nodes).to.have.property('HelloWorld')
        expect(data.settings.unbundleHyps).to.eq(false)
        // TODO: other fields
      })
  })
  it('can get inventory', () => {
    cy.request('GET', '/api/data/test/testgame/inventory')
      .then(res => {
        expect(res.status).to.eq(200)
        return res.body
      })
      .then(data => {
        expect(data.definitions).not.to.eq(null)
        expect(data.definitions.length).not.to.eq(0)
        expect(data.tactics).not.to.eq(null)
        expect(data.tactics.length).not.to.eq(0)
        expect(data.theorems).not.to.eq(null)
        expect(data.theorems.length).not.to.eq(0)
      })
  })
  it('can get level info', () => {
    cy.request('GET', '/api/data/test/testgame/level/HelloWorld/1')
      .then(res => {
        expect(res.status).to.eq(200)
        return res.body
      })
      .then(data => {
        expect(data.title).to.eq('Hello Level')
      })
  })
  it('can get doc item', () => {
    cy.request('GET', '/api/data/test/testgame/doc/theorem/Nat.add_comm')
      .then(res => {
        expect(res.status).to.eq(200)
        return res.body
      })
      .then(data => {
        expect(data.name).to.eq('Nat.add_comm')
        expect(data.displayName).to.eq('add_comm')
      })
  })
  it('can get image', () => {
    cy.request('GET', '/api/data/test/testgame/game')
      .then(res => {
        const image = res.body.worlds.nodes.HelloWorld.image
        expect(image).to.eq('images/sample-bg.png')
        return cy.request('GET', `/api/data/test/testgame/${image}`)
      })
      .then(res => {
        expect(res.status).to.eq(200)
        expect(res.headers['content-type']).to.eq('image/png')
      })
  })
  it('does not serve files outside the images folder', () => {
    cy.request({
      url: '/api/data/test/testgame/images/..%2Fgame.json',
      failOnStatusCode: false,
    }).then(res => {
      expect(res.status).to.eq(404)
    })
  })
  it('can get German language', () => {
    cy.request('GET', '/api/i18n/test/testgame/de')
      .then(res => {
        expect(res.status).to.eq(200)
        return res.body
      })
      .then(data => {
        expect(data['Hello Level']).to.eq('Hallo-Level auf Deutsch')
      })
  })
})

describe('Server communication', () => {
  /** Lean instance shared by all tests in `Server communication`. */
  let instanceId

  /** Checks a proof on the shared Lean instance. */
  function checkProof(input) {
    return cy
      .request('POST', `/api/lean/instances/${instanceId}/check`, input)
      .then(res => {
        expect(res.status).to.eq(200)
        return res.body
      })
  }

  before(() => {
    cy.request('POST', '/api/lean/start/test/testgame').then(res => {
      expect(res.status).to.eq(201)
      expect(res.body.id).to.match(uuidRegex)
      instanceId = res.body.id
    })
  })
  after(() => {
    if (instanceId) cy.request('DELETE', `/api/lean/instances/${instanceId}`)
  })

  it('can start and stop an instance', () => {
    cy.request('POST', '/api/lean/start/test/testgame').then(res => {
      expect(res.status).to.eq(201)
      expect(res.body.id).to.be.an('string')
      expect(res.body.id).to.match(uuidRegex)
      cy.request('DELETE', `/api/lean/instances/${res.body.id}`).then(r => {
        expect(r.status).to.eq(200)
      })
    })
  })
  it('can get status', () => {
    cy.request('GET', `/api/lean/instances/${instanceId}`).then(res => {
      expect(res.status).to.eq(200)
      expect(res.body.status).to.eq('running')
    })
  })
  it('can keep an instance alive', () => {
    cy.request('POST', `/api/lean/instances/${instanceId}/keepalive`).then(
      res => {
        expect(res.status).to.eq(204)
      },
    )
  })
  it('cannot keep an unknown instance alive', () => {
    cy.request({
      method: 'POST',
      url: '/api/lean/instances/00000000-0000-0000-0000-000000000000/keepalive',
      failOnStatusCode: false,
    }).then(res => {
      expect(res.status).to.eq(404)
    })
  })
  it('can stop an instance with POST', () => {
    cy.request('POST', '/api/lean/start/test/testgame').then(res => {
      const id = res.body.id
      cy.request('POST', `/api/lean/instances/${id}/stop`).then(r => {
        expect(r.status).to.eq(200)
      })
      // the instance has exited once its status says so
      const waitForExit = attempts =>
        cy.request('GET', `/api/lean/instances/${id}`).then(r => {
          if (r.body.status !== 'exited' && attempts > 0) {
            cy.wait(200)
            waitForExit(attempts - 1)
          } else {
            expect(r.body.status).to.eq('exited')
          }
        })
      waitForExit(25)
      cy.request({
        method: 'POST',
        url: `/api/lean/instances/${id}/keepalive`,
        failOnStatusCode: false,
      }).then(r => {
        expect(r.status).to.eq(404)
      })
    })
  })
  it('can check empty proof', () => {
    checkProof({
      world: 'HelloWorld',
      level: 1,
      tactics: [],
      inventory: [],
      difficulty: 0,
    }).then(({ completed, completedWithWarnings, steps }) => {
      expect(completed).to.eq(false)
      expect(completedWithWarnings).to.eq(false)
      // only the initial state
      expect(steps).to.have.length(1)
      expect(steps[0].tactic).to.eq('')
      expect(steps[0].goals).to.have.length(1)
      expect(steps[0].goals[0].type).to.eq('x + x = y')
      // unsolved goals
      expect(steps[0].diagnostics.some(d => d.severity === 1)).to.eq(true)
    })
  })
  it('returns hypotheses and hints', () => {
    checkProof({
      world: 'HelloWorld',
      level: 1,
      tactics: [],
      inventory: [],
      difficulty: 0,
    }).then(({ steps }) => {
      const goal = steps[0].goals[0]
      const hyps = Object.fromEntries(
        goal.hyps.flatMap(hyp => hyp.names.map(name => [name, hyp])),
      )
      expect(hyps.h.type).to.eq('x = 2')
      expect(hyps.h.isAssumption).to.eq(true)
      expect(hyps.g.type).to.eq('y = 4')
      expect(hyps.x.type).to.eq('Nat')
      expect(hyps.x.isAssumption).to.eq(false)
      expect(goal.hints.map(hint => hint.text)).to.deep.eq([
        'You can either start using `h` or `g`.',
      ])
    })
  })
  it('can check complete proof', () => {
    checkProof({
      world: 'HelloWorld',
      level: 1,
      tactics: ['rw [g]', 'rw [h]'],
      inventory: [],
      difficulty: 0,
    }).then(({ completed, completedWithWarnings, steps }) => {
      expect(completed).to.eq(true)
      expect(completedWithWarnings).to.eq(true)
      expect(steps.map(step => step.tactic)).to.deep.eq([
        '',
        'rw [g]',
        'rw [h]',
      ])
      expect(steps[1].goals[0].type).to.eq('x + x = 4')
      expect(steps[2].goals).to.have.length(0)
      for (const step of steps) {
        expect(step.diagnostics.filter(d => d.severity === 1)).to.have.length(0)
      }
    })
  })
  it('reports errors at the failing step', () => {
    checkProof({
      world: 'HelloWorld',
      level: 1,
      tactics: ['rw [g]', 'rw [g]'],
      inventory: [],
      difficulty: 0,
    }).then(({ completed, completedWithWarnings, steps }) => {
      expect(completed).to.eq(false)
      expect(completedWithWarnings).to.eq(false)
      expect(steps).to.have.length(3)
      const error = steps[2].diagnostics.find(d => d.severity === 1)
      expect(error).not.to.eq(undefined)
      expect(error.line).to.eq(1)
    })
  })
  it('completes with warnings when using sorry', () => {
    checkProof({
      world: 'HelloWorld',
      level: 1,
      tactics: ['rw [g]', 'sorry'],
      inventory: [],
      difficulty: 0,
    }).then(({ completed, completedWithWarnings, steps }) => {
      expect(completed).to.eq(false)
      expect(completedWithWarnings).to.eq(true)
      expect(steps).to.have.length(3)
      expect(steps[2].goals).to.have.length(0)
      const warning = steps[2].diagnostics.find(d => d.severity === 2)
      expect(warning).not.to.eq(undefined)
      expect(warning.message).to.contain('sorry')
    })
  })
  it('does not keep diagnostics from a previous check', () => {
    checkProof({
      world: 'HelloWorld',
      level: 1,
      tactics: ['rw [g]', 'rw [g]'],
      inventory: [],
      difficulty: 0,
    }).then(({ completed }) => expect(completed).to.eq(false))
    checkProof({
      world: 'HelloWorld',
      level: 1,
      tactics: ['rw [g]', 'rw [h]'],
      inventory: [],
      difficulty: 0,
    }).then(({ completed, steps }) => {
      expect(completed).to.eq(true)
      for (const step of steps) {
        expect(step.diagnostics).to.have.length(0)
      }
    })
  })
  it('can check a shorter proof after a longer one', () => {
    checkProof({
      world: 'HelloWorld',
      level: 1,
      tactics: ['rw [g]', 'rw [h]'],
      inventory: [],
      difficulty: 0,
    }).then(({ steps }) => expect(steps).to.have.length(3))
    checkProof({
      world: 'HelloWorld',
      level: 1,
      tactics: [],
      inventory: [],
      difficulty: 0,
    }).then(({ completed, steps }) => {
      expect(completed).to.eq(false)
      expect(steps).to.have.length(1)
      expect(steps[0].diagnostics.some(d => d.severity === 1)).to.eq(true)
    })
  })
  it('returns the same result when checking the same proof twice', () => {
    const input = {
      world: 'HelloWorld',
      level: 1,
      tactics: ['rw [g]'],
      inventory: [],
      difficulty: 0,
    }
    checkProof(input).then(first => {
      checkProof(input).then(second => {
        expect(second).to.deep.eq(first)
      })
    })
  })
  it('can switch between levels', () => {
    const level1 = {
      world: 'HelloWorld',
      level: 1,
      tactics: ['rw [g]', 'rw [h]'],
      inventory: [],
      difficulty: 0,
    }
    checkProof(level1).then(({ completed }) => expect(completed).to.eq(true))
    checkProof({
      world: 'HelloWorld',
      level: 2,
      tactics: ['rw [h]'],
      inventory: [],
      difficulty: 0,
    }).then(({ completed }) => expect(completed).to.eq(true))
    checkProof(level1).then(({ completed }) => expect(completed).to.eq(true))
  })
  it('returns no hover information unless requested', () => {
    checkProof({
      world: 'HelloWorld',
      level: 1,
      tactics: [],
      inventory: [],
      difficulty: 0,
    }).then(({ steps, hovers, hoverDocs }) => {
      expect(hovers).to.have.length(0)
      expect(hoverDocs).to.have.length(0)
      const goal = steps[0].goals[0]
      expect(goal.typeWithHover).to.eq(null)
      expect(goal.hyps[0].typeWithHover).to.eq(null)
    })
  })
  it('returns hover information', () => {
    checkProof({
      world: 'HelloWorld',
      level: 1,
      tactics: [],
      inventory: [],
      difficulty: 0,
      hovers: true,
    }).then(({ steps, hovers, hoverDocs }) => {
      const goal = steps[0].goals[0]
      expect(flatten(goal.typeWithHover)).to.eq(goal.type)
      for (const hyp of goal.hyps) {
        expect(flatten(hyp.typeWithHover)).to.eq(hyp.type)
      }
      // `x + x = y`: the outer tag spans the whole equation, so hovering `=`
      // highlights both sides
      const [eq, eqCode] = goal.typeWithHover.tag
      expect(hovers[eq].type).to.eq('Prop')
      const [lhs, op, rhs] = eqCode.append
      expect(op).to.deep.eq({ text: ' = ' })
      expect(flatten(lhs)).to.eq('x + x')
      expect(hovers[lhs.tag[0]].type).to.eq('Nat')
      expect(hovers[rhs.tag[0]].expr).to.eq('y')
      // the same `x` shares one entry
      const [x1, , x2] = lhs.tag[1].append
      expect(x1.tag[0]).to.eq(x2.tag[0])
      expect(hovers[x1.tag[0]].type).to.eq('Nat')
      expect(hoverDocs[hovers[eq].doc]).to.contain('equality')
    })
  })
  it('shares hover information between steps', () => {
    checkProof({
      world: 'HelloWorld',
      level: 1,
      tactics: ['replace h := h.symm'],
      inventory: [],
      difficulty: 0,
      hovers: true,
    }).then(({ steps, hovers }) => {
      const hypH = step =>
        steps[step].goals[0].hyps.find(hyp => hyp.names.includes('h'))
      const before = hypH(0).typeWithHover
      const after = hypH(1).typeWithHover
      // the replaced `h` gets a new entry ...
      expect(before.tag[0]).not.to.eq(after.tag[0])
      expect(hovers[before.tag[0]].expr).to.eq('@Eq Nat x 2')
      expect(hovers[after.tag[0]].expr).to.eq('@Eq Nat 2 x')
      // `replace` creates a non-dependent `let` whose value isn't shown
      expect(hypH(1).value).not.to.exist()
      // ... while the unchanged goal is shared
      expect(steps[1].goals[0].typeWithHover).to.deep.eq(
        steps[0].goals[0].typeWithHover,
      )
      // each distinct subexpression is stored only once
      const indices = new Set()
      const collect = code => {
        if ('text' in code) return
        if ('append' in code) {
          code.append.forEach(collect)
          return
        }
        indices.add(code.tag[0])
        collect(code.tag[1])
      }
      for (const step of steps) {
        for (const goal of step.goals) {
          collect(goal.typeWithHover)
          goal.hyps.forEach(hyp => collect(hyp.typeWithHover))
        }
      }
      expect(indices.size).to.eq(hovers.length)
    })
  })
  it('replaces a waiting check by a newer one', () => {
    const post = tactics =>
      fetch(`/api/lean/instances/${instanceId}/check`, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          world: 'HelloWorld',
          level: 1,
          tactics,
          inventory: [],
          difficulty: 0,
        }),
      }).then(async res => ({ status: res.status, body: await res.json() }))
    // parallel requests may reach the server in any order, so the later ones are delayed
    const after = (ms, tactics) =>
      new Promise(resolve => setTimeout(resolve, ms)).then(() => post(tactics))
    // `running` keeps Lean busy while the other two arrive
    const runningPromise = post(['sleep 3000'])
    const replacedPromise = after(300, ['rw [g]'])
    const newestPromise = after(600, ['rw [g]', 'rw [h]'])
    cy.wrap(Promise.all([runningPromise, replacedPromise, newestPromise]), {
      timeout: 120_000,
    }).then(([running, replaced, newest]) => {
      expect(running.status).to.eq(200)
      expect(replaced.status).to.eq(409)
      expect(newest.status).to.eq(200)
      expect(newest.body.completed).to.eq(true)
    })
  })
})

describe('Statistics', () => {
  /** Lean instance for the tests which need a check */
  let statsInstanceId

  before(() => {
    cy.request('POST', '/api/lean/start/test/testgame').then(res => {
      expect(res.status).to.eq(201)
      statsInstanceId = res.body.id
    })
  })
  after(() => {
    if (statsInstanceId) {
      cy.request('DELETE', `/api/lean/instances/${statsInstanceId}`)
    }
  })
  it('counts checks in the play statistics', () => {
    cy.request({
      method: 'POST',
      url: `/api/lean/instances/${statsInstanceId}/check`,
      headers: { 'Accept-Language': 'fr-CH,fr;q=0.9,en;q=0.8' },
      body: {
        world: 'HelloWorld',
        level: 1,
        tactics: ['rw [g]'],
        inventory: [],
        difficulty: 0,
        language: 'de',
      },
    })
    cy.request('GET', '/stats/games').then(res => {
      const rows = res.body.filter(
        row =>
          row.owner === 'test' &&
          row.repo === 'testgame' &&
          row.language === 'de' &&
          row.preferredLanguage === 'fr',
      )
      expect(rows).to.have.length.of.at.least(1)
    })
  })
  it('can list play statistics', () => {
    cy.request('GET', '/stats/games?from=2026-01-01').then(res => {
      expect(res.status).to.eq(200)
      expect(res.body).to.be.an('array')
      for (const row of res.body) {
        expect(row).to.have.all.keys(
          'interval',
          'owner',
          'repo',
          'language',
          'preferredLanguage',
          'sessions',
          'checks',
          'playSeconds',
        )
      }
    })
  })
  it('can list import statistics', () => {
    cy.request('GET', '/stats/imports').then(res => {
      expect(res.status).to.eq(200)
      expect(res.body).to.be.an('array')
      for (const game of res.body) {
        expect(game).to.have.all.keys(
          'owner',
          'repo',
          'toolchain',
          'leanVersion',
          'firstImportedAt',
          'lastImportedAt',
          'importCount',
          'importsPerDay',
          'fullyBuilt',
        )
      }
    })
  })
})
