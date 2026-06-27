# Development

## Updating Lean version

1. make sure `lean-i18n` has been updated
1. edit `server/lean-toolchain` to contain the desired version: `leanprover/lean4:v4.31.0`
2. edit all `require` statements in `server/lakefile.lean` to contain the toolchain (e.g. `"v4.31.0"`) instead of `"main"`
3. call `lake update --keep-toolchain`
4. undo the changes in `server/lakefile.lean`
5. `npm run build:server`
