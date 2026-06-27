# Development

## Updating Lean version

1. make sure `lean-i18n` has been updated
2. edit `server/lean-toolchain` to contain the desired version: `leanprover/lean4:v4.31.0`
3. edit all `require` statements in `server/lakefile.lean` to contain the toolchain (e.g. `"v4.31.0"`) instead of `"main"`
4. call `lake update --keep-toolchain`
5. undo the changes in `server/lakefile.lean`
6. `npm run build:server`
7. on github, create a PR and merge it
8. create a tag, e.g. `v4.31.0`, pointing to the bump commit
