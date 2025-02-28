describe('The world selection', () => {
  it('displays the game title', () => {
    cy.visit('http://localhost:3000/#/g/test/Test')
    cy.contains('span.nav-title', 'Test Game').should('exist')
  })

  it('displays the rules popup', () => {
    cy.visit('http://localhost:3000/#/g/test/Test')
    cy.contains('a.nav-button', 'Rules').click()
    cy.contains('div.modal', 'Game Rules').should('exist')
  })

  it('displays the world titles', () => {
    cy.visit('http://localhost:3000/#/g/test/Test')
    cy.get('p.world-title')
        .map('textContent')
        .should('have.members', ['Demo World 1', 'Demo World 2']);
  })

  it('displays the first world and its first level as selectable', () => {
    cy.visit('http://localhost:3000/#/g/test/Test')
    const world = cy.contains('svg.world-selection>a:not(.disabled)', 'Demo World 1')
    const assertOn = [world, world.next('a.level')]

    assertOn.forEach((value) => value
        .should('have.attr', 'href', '#/g/test/Test/world/DemoWorld1/level/0')
        .and('have.css', 'cursor', 'pointer')
    )
  })

  it('displays the second world and its first level as disabled', () => {
    cy.visit('http://localhost:3000/#/g/test/Test')
    const world = cy.contains('svg.world-selection>a.disabled', 'Demo World 2')
    const assertOn = [world, world.next('a.level.disabled')]

    assertOn.forEach((value) => value
        .should('have.attr', 'href', '#/g/test/Test')
        .and('have.css', 'cursor', 'default')
    )
  })
})