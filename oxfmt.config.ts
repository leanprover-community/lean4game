import { defineConfig } from 'oxfmt'

export default defineConfig({
  ignorePatterns: ['**/lake-manifest.json', '**/.lake/', '**/.i18n/'],
  printWidth: 80,
  semi: false,
  singleQuote: true,
  sortImports: true,
  sortTailwindcss: { stylesheet: './client/src/index.css' },
  trailingComma: 'all',
  arrowParens: 'avoid',
  tabWidth: 2,
  useTabs: false,
  endOfLine: 'lf',
  bracketSpacing: true,
  insertFinalNewline: true,
})
