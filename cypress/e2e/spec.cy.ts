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
    cy.contains('svg.world-selection>a:not(.disabled)', 'Demo World 1').as('world').next('a.level').as('level')
    cy.get('@world')
        .should('have.attr', 'href', '#/g/test/Test/world/DemoWorld1/level/0')
        .and('have.css', 'cursor', 'pointer')
    cy.get('@level')
        .should('have.attr', 'href', '#/g/test/Test/world/DemoWorld1/level/0')
        .and('have.css', 'cursor', 'pointer')
  })

  it('displays the second world and its first level as disabled', () => {
    cy.visit('http://localhost:3000/#/g/test/Test')
    cy.contains('svg.world-selection>a.disabled', 'Demo World 2').as('world').next('a.level.disabled').as('level')
    cy.get('@world')
        .should('have.attr', 'href', '#/g/test/Test')
        .and('have.css', 'cursor', 'default')
    cy.get('@level')
        .should('have.attr', 'href', '#/g/test/Test')
        .and('have.css', 'cursor', 'default')
  })
})

describe('The first level', () => {
  it('can be navigated to from the world selection', () => {
    cy.visit('http://localhost:3000/#/g/test/Test')
    cy.contains('p.world-title', 'Demo World 1').click()
    cy.location().its("hash").should('eq', '#/g/test/Test/world/DemoWorld1/level/0')
  })

  it('displays world and level title', () => {
    cy.visit('http://localhost:3000/#/g/test/Test/world/DemoWorld1/level/0')
    cy.contains('div.nav-content', 'Demo World 1')
        .children()
        .map((v) => v.textContent.trim())
        .should('have.members', ['Demo World 1', 'Introduction', 'Start'])
  })

  it('displays the inventory tabs', () => {
    cy.visit('http://localhost:3000/#/g/test/Test/world/DemoWorld1/level/0')
    cy.get('div.tab')
        .map((v) => v.textContent.trim())
        .should('have.members', ['Theorems', 'Tactics', 'Definitions'])
  })

  it('displays the theorems inventory', () => {
    cy.visit('http://localhost:3000/#/g/test/Test/world/DemoWorld1/level/0')
    cy.contains('div.tab', 'Theorems').click()
    cy.contains('div.inventory-list>div.item', 'demo_statement').click()
    cy.contains('div.documentation>h1', 'demo_statement').should('exist')
    cy.get('div.documentation>*>svg.fa-xmark').click()
  })

  it('displays the tactics inventory', () => {
    cy.visit('http://localhost:3000/#/g/test/Test/world/DemoWorld1/level/0')
    cy.contains('div.tab', 'Tactics').click()
    cy.get('div.inventory-list>div.item')
        .map((v) => v.textContent.trim())
        .should('have.members', ['exact', 'rfl', 'rw'])
    cy.contains('div.inventory-list>div.item', 'exact').click()
    cy.contains('div.documentation>h1', 'exact').should('exist')
    cy.get('div.documentation>div.markdown')
        .contains('exact e closes the main goal if its target type matches that of e.')
        .should('exist')
  })
})