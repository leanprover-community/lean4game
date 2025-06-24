describe('Test application', () => {
  it('opens the Test Game, World and Level', () => {
    cy.visit('/#/g/test/TestGame')
    cy.contains('This is the introduction text of the game.')
    cy.contains('Test World')
    cy.contains('1').click()
    cy.contains('This is the introduction of Test World.')
    cy.contains('Start').click()
    cy.contains('Goal:')
  })
})
