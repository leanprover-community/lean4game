import { defineConfig } from 'cypress'

export default defineConfig({
  e2e: {
    baseUrl: 'http://localhost:3000',
    supportFile: false,
    // Lean checks can be slow on a cold or busy server;
    // match the server's default `LEAN_CHECK_TIMEOUT_MS`
    responseTimeout: 120_000,
    defaultCommandTimeout: 10_000,
  },
  allowCypressEnv: false,
})
