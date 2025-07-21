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

  // Helper function to navigate to introduction page
  const navigateToIntroduction = () => {
    cy.contains('Test World').click({ force: true })
    cy.url().should('include', '/level/0')  // Wait for navigation
  }

  // Helper function to navigate to level
  const navigateToLevel = () => {
    navigateToIntroduction()
    cy.contains('Start').click()
    cy.contains('Goal:', { timeout: 60000 })
  }

  describe('Navigation and UI Structure', () => {
    it('should navigate to world introduction via Test World button', () => {
      navigateToIntroduction()

      // Check we're on the introduction page with correct title
      cy.contains('Introduction').should('be.visible')
      cy.contains('This is the introduction of Test World.')
    })

    it('should navigate to world introduction via level 1 button', () => {
      // Click on level 1 directly
      cy.contains('1').click({ force: true })
      cy.url().should('include', '/level/0')  // Wait for navigation

      // Check we're on the introduction page with correct title
      cy.contains('Introduction').should('be.visible')
      cy.contains('This is the introduction of Test World.')
    })

    it('should navigate from introduction to level', () => {
      navigateToLevel()

      // Verify we're in the level with Monaco editor and goal
      cy.get('.monaco-editor').should('be.visible')
      cy.contains('Active Goal').should('be.visible')
    })
  })

  describe('Hints and Progressive Guidance', () => {
    it('should show initial hint after starting level', () => {
      navigateToLevel()

      // Check for the initial hint (should be the only hint visible)
      cy.contains('You can either start using').should('be.visible')

      // Verify no other hints are shown initially
      cy.contains('You should use g now').should('not.exist')
    })

    it('should show progressive hint after first tactic', () => {
      navigateToLevel()

      // Enter first tactic
      cy.get('.typewriter-input .monaco-editor .view-lines').click({ force: true })
      cy.focused().type('rw [h]{enter}')

      // Wait for the goal state to update after first tactic
      cy.contains('2 + 2 = y', { timeout: 10000 }).should('be.visible')

      // Check that the progressive hint appears
      cy.contains('You should use g now').should('be.visible')
    })
  })

  describe('Tactics Panel and Documentation', () => {
    it('should display tactics panel with rfl and rw buttons', () => {
      navigateToLevel()

      // Check that tactics section exists
      cy.contains('Tactics').should('be.visible')

      // Check for the specific tactics buttons
      cy.get('.inventory').within(() => {
        cy.contains('rfl').should('be.visible')
        cy.contains('rw').should('be.visible')
      })
    })

    it('should show rfl documentation when clicked', () => {
      navigateToLevel()

      // Click on rfl button in tactics panel
      cy.get('.inventory').within(() => {
        cy.contains('rfl').click()
      })

      // Check for the rfl docstring (We don't check for the exact text, because it can change)
      cy.contains('reflexivity').should('be.visible')
      cy.contains('(lean docstring)').should('be.visible')
    })
  })

  describe('Tactic Input and Goal Updates', () => {
    it('should accept tactic input and update goal state', () => {
      navigateToLevel()

      // Use typewriter interface (blue box at bottom)
      cy.get('.typewriter-input .monaco-editor .view-lines').click({ force: true })
      cy.focused().type('rw [h]{enter}')

      // Wait for Lean to process the tactic
      // Should show updated goal state (proving the tactic was processed)
      cy.contains('2 + 2 = y', { timeout: 10000 }).should('be.visible')
    })
  })

  describe('Level Completion', () => {
    it('should complete the test level with proper solution', () => {
      navigateToLevel()

      // Solve the level step by step (based on the Lean file)
      cy.get('.typewriter-input .monaco-editor .view-lines').click({ force: true })
      cy.focused().type('rw [h]{enter}')

      // Wait for the goal state to update after first tactic
      cy.contains('2 + 2 = y', { timeout: 10000 }).should('be.visible')

      // Enter second tactic
      cy.get('.typewriter-input .monaco-editor .view-lines').click({ force: true })
      cy.focused().type('rw [g]{enter}')

      // Look for the completion message from the Lean file
      cy.contains('This last message appears if the level is solved.', { timeout: 60000 })
    })
  })

  describe('Settings and Preferences', () => {
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
})
