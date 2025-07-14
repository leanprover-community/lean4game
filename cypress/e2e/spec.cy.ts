describe('Test application', () => {
  it('opens the Test Game, World and Level', () => {
    cy.visit('/#/g/test/TestGame')
    cy.contains('This is the introduction text of the game.')
    cy.contains('Test World')
    cy.contains('1').click()
    cy.contains('This is the introduction of Test World.')
    cy.contains('Start').click()
    
    // Wait much longer for the Lean server to load the level
    cy.contains('Goal:', { timeout: 60000 })  // 60 seconds timeout
  })
})
