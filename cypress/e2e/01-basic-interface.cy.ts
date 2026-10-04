// cypress/e2e/basic-game-features.cy.ts
// Tests for basic game functionality using the simple TestGame

describe('Basic Lean4game Interface', () => {
  describe('Error Page', () => {
    beforeEach(() => {
      cy.visit('/#/not-found')
      cy.get('#error-page').should('be.visible')
    })
    it('contains a valid link', () => {
      cy.get('#error-page a')
        .should('have.attr', 'target', '_blank')
        .then($a => {
          const href = $a.prop('href')
          cy.request(href).its('status').should('eq', 200)
        })
    })
    it('background image exists', () => {
      cy.get('#error-page')
        .should('have.css', 'background-image')
        .and('not.eq', 'none')
        .then((bg: any) => {
          const urlMatch = bg.match(/url\(["']?(.*?)["']?\)/)
          expect(urlMatch).to.not.be.null
          const imageUrl = urlMatch[1]
          // If the imageUrl is relative, convert to absolute
          const absoluteUrl = imageUrl.startsWith('http') ? imageUrl : `${Cypress.config().baseUrl}${imageUrl}`
          cy.request(absoluteUrl).its('status').should('eq', 200)
        })
    })
  })
  describe('Popup', () => {
    describe('Erase', () => {})
    describe('Impressum', () => {
      it('landing page footer', () => {
        cy.visit('/#/')
        cy.get('footer').contains('a', 'Impressum').should('be.visible').click()
        cy.contains('a', 'Contact Details').should('have.attr', 'target', '_blank')
        .then($a => {
          const href = $a.prop('href')
          cy.request(href).its('status').should('eq', 200)
        })
      })
    })
    describe('Info', () => {
      it('shows the progress saving notice once', () => {
        cy.visit('/#/g/test/TestGame')
        cy.get('#menu-btn').click()
        cy.contains('.menu.dropdown .btn', 'Game Info').click()
        cy.contains('h2', 'Progress saving').should('be.visible')
        cy.get('.welcome-text').invoke('text').then(text => {
          expect(text.split('The game stores your progress').length - 1).to.eq(1)
        })
      })
    })
    describe('Preferences', () => {})
    describe('Privacy', () => {
      it('landing page footer', () => {
        cy.visit('/#/')
        cy.get('footer').contains('a', 'Privacy Policy').should('be.visible').click()
        cy.contains('a', 'Contact Details').should('have.attr', 'target', '_blank')
        .then($a => {
          const href = $a.prop('href')
          cy.request(href).its('status').should('eq', 200)
        })
      })
    })
    describe('Rules', () => {
      it('can be opened from world tree', () => {
        cy.visit('/#/g/test/TestGame')
        cy.get('.difficulty-label').find('.helpButton').should('be.visible').click()
        cy.contains('🔐')
        cy.contains('🔓')
      })
    })
    describe('Upload', () => {})
  })
})
