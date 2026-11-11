# Development

## Deploying GameSkeleton and GameServer

initial setup; add the desired remote once:

```bash
git remote add gameskeleton git@github.com:hhu-adam/GameSkeleton.git
git fetch gameskeleton
git remote add gameserver git@github.com:hhu-adam/GameServer.git
git fetch gameserver
```

Then, the content of `GameSkeleton/` and `server/lean` can be pushed to these repos with

```bash
git subtree push --prefix=GameSkeleton gameskeleton main
git subtree push --prefix=server/lean gameserver main
```

## Pushing Tags

The important tag for the users is the one on `gameserver`.

```
git tag v4.35.0
git push origin v4.35.0
git push gameserver "$(git subtree split --prefix=server/lean v4.35.0)":refs/tags/v4.35.0
```

## Updating Lean version

1. make sure `lean-i18n` has been updated
2. edit `server/lean/lean-toolchain` to contain the desired version: `leanprover/lean4:v4.31.0`
3. edit all `require` statements in `server/lean/lakefile.lean` to contain the toolchain (e.g. `"v4.31.0"`) instead of `"main"`
4. call `lake update --keep-toolchain`
5. undo the changes in `server/lean/lakefile.lean`
6. `npm run build:server`
7. on github, create a PR and merge it
8. create a tag, e.g. `v4.31.0`, pointing to the bump commit
