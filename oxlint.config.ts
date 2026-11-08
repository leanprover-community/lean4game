import { defineConfig } from 'oxlint'

export default defineConfig({
  options: { typeAware: true },
  plugins: [
    'typescript',
    'unicorn',
    'oxc',
    'node',
    'import',
    'react',
    'react-perf',
    'jsx-a11y',
  ],
  categories: {
    correctness: 'warn',
    perf: 'off',
    style: 'off',
    restriction: 'off',
    pedantic: 'off',
    suspicious: 'warn',
  },
  rules: {
    'react/react-in-jsx-scope': 'off', // not relevant for React 17+
    'oxc/no-async-endpoint-handlers': 'off', // not relevant for Express 5+
    'typescript/no-unsafe-type-assertion': 'off', // e.g. `err as Error` in `catch`
    'import/no-unassigned-import': 'off',
    'import/no-named-as-default-member': 'off', // e.g. `i18n.use(...)` of i18next
    'import/no-cycle': 'warn',
    'import/no-duplicates': 'warn',
    'typescript/switch-exhaustiveness-check': 'warn',
    'typescript/require-await': 'warn',
    'typescript/return-await': 'warn',
    'typescript/only-throw-error': 'warn',
    'typescript/no-deprecated': 'warn',
    'typescript/no-unnecessary-condition': 'warn',
    'unicorn/prefer-node-protocol': 'warn',
    'unicorn/numeric-separators-style': 'warn',
    'unicorn/catch-error-name': 'warn',
    eqeqeq: ['warn', 'smart'],
  },
})
