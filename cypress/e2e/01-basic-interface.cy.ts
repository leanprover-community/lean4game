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
    describe('Erase', () => {
      it('opens erase popup and shows download and delete options', () => {
        cy.visit('/#/g/test/TestGame')
        cy.get('#menu-btn').click()
        cy.contains('.menu.dropdown .btn', 'Erase').click()
        cy.contains('h2', 'Delete Progress?').should('be.visible')
        cy.contains('Download & Delete everything').should('be.visible')
      })
    })
    describe('Download', () => {
      it('renders download button in dropdown menu and downloads non-empty progress JSON', () => {
        cy.visit('/#/g/test/TestGame')
        cy.get('#menu-btn').click()
        cy.contains('.menu.dropdown .btn', 'Download').should('be.visible').click()
        const now = new Date()
        const dateStr = `${now.getFullYear()}-${String(now.getMonth() + 1).padStart(2, '0')}-${String(now.getDate()).padStart(2, '0')}`
        const downloadsFolder = Cypress.config('downloadsFolder')
        cy.readFile(`${downloadsFolder}/lean4game-test_TestGame-${dateStr}.json`).then((content) => {
          expect(content).to.be.an('object')
          expect(content).to.have.property('inventory')
          expect(content).to.have.property('data')
        })
      })
    })
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
    describe('Upload', () => {
      it('opens upload popup and displays progress upload options', () => {
        cy.visit('/#/g/test/TestGame')
        cy.get('#menu-btn').click()
        cy.contains('.menu.dropdown .btn', 'Upload').click()
        cy.contains('h2', 'Upload Saved Progress').should('be.visible')
        cy.contains('downloading your current progress').should('be.visible')
      })
      it('uploads progress JSON and persists it to localStorage', () => {
        cy.visit('/#/g/test/TestGame')
        cy.get('#menu-btn').click()
        cy.contains('.menu.dropdown .btn', 'Upload').click()
        const sampleProgress = {
          inventory: ['rfl'],
          data: {
            World1: {
              readIntro: true,
              1: { code: 'rfl\n', selections: [], completed: true, help: [] }
            }
          },
          readIntro: true,
          difficulty: 2
        }
        cy.get('.modal input[type="file"]').selectFile({
          contents: Cypress.Buffer.from(JSON.stringify(sampleProgress)),
          fileName: 'lean4game-test_TestGame-2026-01-01.json',
          mimeType: 'application/json'
        })
        cy.contains('.modal button', 'Load selected file').should('not.be.disabled').click()
        cy.get('.modal').should('not.exist')
        cy.window().then((win) => {
          const raw = win.localStorage.getItem('game_progress')
          expect(raw).to.not.be.null
          const parsed = JSON.parse(raw!)
          expect(parsed.games['g/test/TestGame'].inventory).to.deep.equal(['rfl'])
          expect(parsed.games['g/test/TestGame'].data.World1['1'].completed).to.equal(true)
        })
      })
    })
  })
})
