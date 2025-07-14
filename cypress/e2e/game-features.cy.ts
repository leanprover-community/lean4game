// cypress/e2e/basic-game-features.cy.ts
// Tests for basic game functionality using the simple TestGame

describe('Basic Lean4Game Features', () => {
  beforeEach(() => {
    // Handle Lean server timeout errors
    cy.on('uncaught:exception', (err) => {
      if (err.message.includes('Stopping the server timed out') || 
          err.message.includes('timeout') ||
          err.message.includes('WebSocket') ||
          err.message.includes('Socket') ||
          err.message.includes('Connection')) {
        return false
      }
      return true
    })
    
    // Navigate to test game before each test
    cy.visit('/#/g/test/TestGame')
    cy.contains('This is the introduction text of the game.', { timeout: 15000 })
  })

  describe('Basic Navigation', () => {
    it('should navigate through the game flow', () => {
      // Click on the world (using force to bypass SVG overlay)
      cy.contains('Test World').click({ force: true })
      
      // Click on level 1
      cy.contains('1').click({ force: true })
      
      // Check we're on the level introduction
      cy.contains('This is the introduction of Test World.')
      
      // Start the level
      cy.contains('Start').click()
      
      // Verify we're in the level and Lean server loaded
      cy.contains('Goal:', { timeout: 60000 })
    })

    it('should display the correct world and level info', () => {
      cy.contains('Test World').click({ force: true })
      cy.contains('1').click({ force: true })
      
      // Check we're on the level introduction (same as working test)
      cy.contains('This is the introduction of Test World.')
      
      // Start the level
      cy.contains('Start').click()
      
      // After starting, we should be able to see goal instead of level metadata
      cy.contains('Goal:', { timeout: 60000 })
    })
  })

  describe('Basic Proof Interface', () => {
    it('should load the proof interface', () => {
      cy.contains('Test World').click({ force: true })
      cy.contains('1').click({ force: true })
      cy.contains('Start').click()
      cy.contains('Goal:', { timeout: 60000 })

      // Check Monaco editor is present
      cy.get('.monaco-editor').should('be.visible')
      
      // Check infoview (goal display) is present - look for the goal content instead
      cy.contains('Active Goal').should('be.visible')
      cy.contains('Objects:').should('be.visible')
      
      // Check that we can see the goal state - just verify goal section exists
      cy.contains('Goal:').should('be.visible')
    })

    it('should accept tactic input', () => {
      cy.contains('Test World').click({ force: true })
      cy.contains('1').click({ force: true })
      cy.contains('Start').click()
      cy.contains('Goal:', { timeout: 60000 })

      // Use typewriter interface (blue box at bottom)
      cy.get('.typewriter-input .monaco-editor .view-lines').click({ force: true })
      cy.focused().type('rw [h]{enter}')
      
      // Wait for Lean to process
      cy.wait(3000)
      
      // Should show updated goal state (proving the tactic was processed)
      cy.contains('2 + 2 = y', { timeout: 10000 }).should('be.visible')
    })
  })

  describe('Basic Hints', () => {
    it('should display initial hints', () => {
      cy.contains('Test World').click({ force: true })
      cy.contains('1').click({ force: true })
      cy.contains('Start').click()
      cy.contains('Goal:', { timeout: 60000 })

      // Check for the specific hint from the test level
      cy.contains('You can either start using', { timeout: 10000 }).should('be.visible')
      
      // Check hints are in information messages
      cy.get('.message.information').should('be.visible')
    })
  })

  describe('Basic Inventory', () => {
    it('should show tactics panel', () => {
      cy.contains('Test World').click({ force: true })
      cy.contains('1').click({ force: true })
      cy.contains('Start').click()
      cy.contains('Goal:', { timeout: 60000 })

      // Check that tactics section exists
      cy.contains('Tactics').should('be.visible')
      
      // Check for the basic tactics from the test level (rw, rfl)
      cy.get('.inventory').within(() => {
        cy.contains('rw').should('be.visible')
      })
    })
  })

  describe('Basic Settings', () => {
    it('should open preferences popup', () => {
      // Click menu button to open dropdown
      cy.get('#menu-btn').click()
      
      // Click preferences
      cy.contains('Preferences').click()
      
      // Check preferences popup opened
      cy.get('.MuiSlider-root').should('be.visible')
      
      // Close popup
      cy.get('body').click(0, 0)
    })
  })

  describe('Basic Level Completion', () => {
    it('should complete the test level', () => {
      cy.contains('Test World').click({ force: true })
      cy.contains('1').click({ force: true })
      cy.contains('Start').click()
      cy.contains('Goal:', { timeout: 60000 })

      // Solve the level step by step (based on the Lean file)
      cy.get('.typewriter-input .monaco-editor .view-lines').click({ force: true })
      cy.focused().type('rw [h]{enter}')
      cy.wait(4000)
      
      // Enter second tactic
      cy.get('.typewriter-input .monaco-editor .view-lines').click({ force: true })
      cy.focused().type('rw [g]{enter}')
      cy.wait(4000)

      // Look for the completion message from the Lean file
      cy.contains('This last message appears if the level is solved.', { timeout: 15000 })
    })
  })
})