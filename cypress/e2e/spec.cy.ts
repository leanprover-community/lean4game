describe('Test Game', () => {
  it('displays the world overview', () => {
    cy.visit('http://localhost:3000/#/g/test/Test')
    cy.contains('p.world-title', 'Demo World 1').should('exist');
    cy.contains('p.world-title', 'Demo World 2').should('exist');
  })
})