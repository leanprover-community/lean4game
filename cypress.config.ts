import { defineConfig } from "cypress";

// default timeout was 4000.
// Infoview loading is slow on Windows…

export default defineConfig({
  defaultCommandTimeout: 40000,
  experimentalWebKitSupport: true,
  e2e: {
    setupNodeEvents(on, config) {
      // implement node event listeners here
    },
  },
});
