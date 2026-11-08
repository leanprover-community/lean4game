/** Players of the old client have their progress in local storage in this form */
const oldLevel = (code, completed = true) => ({
  code,
  selections: [],
  completed,
  help: [],
})

const oldGame = data => ({
  inventory: [],
  difficulty: 0,
  readIntro: true,
  data,
})

const LEVEL = '/g/test/testgame/helloworld/1'
const LEAN_TIMEOUT = 120_000

function visitWithProgress(games, path = LEVEL) {
  cy.visit(path, {
    onBeforeLoad(win) {
      win.localStorage.setItem('game_progress', JSON.stringify({ games }))
    },
  })
}

const storedGames = () =>
  cy
    .window()
    .then(win => JSON.parse(win.localStorage.getItem('game_progress')).games)

describe('Progress of the old client', () => {
  it('finds a game stored in the spelling of the URL', () => {
    visitWithProgress({
      'g/test/TestGame': oldGame({
        HelloWorld: { readIntro: true, 1: oldLevel('rw [h]\nrw [g]\n') },
      }),
    })
    cy.contains('rw [g]', { timeout: LEAN_TIMEOUT })
    storedGames().then(games => {
      expect(Object.keys(games)).to.deep.equal(['g/test/testgame'])
      const level = games['g/test/testgame'].data.HelloWorld[1]
      expect(level.code).to.equal('rw [h]\nrw [g]\n')
      expect(level.completed).to.equal(true)
    })
  })

  it('merges the spellings of a game', () => {
    visitWithProgress({
      'g/test/TestGame': oldGame({
        HelloWorld: { readIntro: true, 1: oldLevel('rw [h]\nrw [g]\n') },
      }),
      'g/test/testgame': {
        ...oldGame({
          HelloWorld: { readIntro: false, 2: oldLevel('rfl\n', false) },
        }),
        difficulty: 1,
      },
    })
    storedGames().then(games => {
      expect(Object.keys(games)).to.deep.equal(['g/test/testgame'])
      const game = games['g/test/testgame']
      expect(game.difficulty).to.equal(1)
      expect(game.data.HelloWorld.readIntro).to.equal(true)
      expect(game.data.HelloWorld[1].completed).to.equal(true)
      expect(game.data.HelloWorld[2].code).to.equal('rfl\n')
    })
  })

  it('fills in what older versions did not store', () => {
    visitWithProgress({
      'g/test/TestGame': {
        data: { HelloWorld: { 1: { code: 'rw [h]\n', completed: false } } },
      },
    })
    // revealing a hint fails if the level has no `help`
    cy.contains('button', 'Next hint', { timeout: LEAN_TIMEOUT }).click()
    cy.contains('Hidden Hint 1')
    storedGames().then(games => {
      const game = games['g/test/testgame']
      expect(game.inventory).to.deep.equal([])
      expect(game.data.HelloWorld[1].help).to.deep.equal([1])
    })
  })

  it('keeps a malformed game and still migrates the others', () => {
    const broken = { inventory: 'not a list', data: 'nothing' }
    visitWithProgress({
      'g/other/Broken': broken,
      'g/test/TestGame': oldGame({
        HelloWorld: { readIntro: true, 1: oldLevel('rw [h]\nrw [g]\n') },
      }),
    })
    cy.contains('rw [g]', { timeout: LEAN_TIMEOUT })
    storedGames().then(games => {
      expect(games['g/other/Broken']).to.deep.equal(broken)
      expect(games['g/test/testgame'].data.HelloWorld[1].completed).to.equal(
        true,
      )
    })
  })

  it('leaves migrated progress as it is on the next visit', () => {
    visitWithProgress({
      'g/test/TestGame': oldGame({
        HelloWorld: { readIntro: true, 1: oldLevel('rw [h]\nrw [g]\n') },
      }),
    })
    cy.contains('rw [g]', { timeout: LEAN_TIMEOUT })
    storedGames().then(before => {
      cy.reload()
      cy.contains('rw [g]', { timeout: LEAN_TIMEOUT })
      storedGames().then(after => expect(after).to.deep.equal(before))
    })
  })

  it('does not solve a level because of the unlocked items', () => {
    visitWithProgress({
      'g/test/TestGame': {
        ...oldGame({
          HelloWorld: { readIntro: true, 1: oldLevel('exact foo\n', false) },
        }),
        inventory: ['rw', 'rfl', 'Nat.add_comm'],
      },
    })
    cy.contains('Failed command', { timeout: LEAN_TIMEOUT })
    storedGames().then(games => {
      expect(games['g/test/testgame'].data.HelloWorld[1].completed).to.equal(
        false,
      )
    })
  })
})
