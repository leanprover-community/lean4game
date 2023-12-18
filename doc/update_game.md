# How to update your Game

## New Lean version

You can update the game to any Lean version by simply editing the `lean-toolchain` in your game repo to contain the
new lean version `leanprover/lean4:v4.X.0`.

Before you continue, make sure there [exists a `v4.X.0`-tag in this repo](https://github.com/leanprover-community/lean4game/tags).

Then, depending on the setup you use, do one of the following:

* **Dev Container**: Rebuild the VSCode Devcontainer (without Cache!).
* **Local Setup**: in your game's folder run the following:
  ```
  lake update -R
  lake build
  ```

  * Additionally, if you have a local copy of the server `lean4game`,
    you should update this one to the matching version. Run the following in the folder `lean4game/`:
    ```
    git fetch
    git checkout {VERSION_TAG}
    npm install
    ```
    where `{VERSION_TAG}` is the tag from above of the form `v4.X.0`
* **Gitpod/Codespaces**: Create a fresh one

This will update your game (and the mathlib version you might be using) to the new lean version.

## Newest developing setup

There are a few files in your game repository which are used for the developing setup
(dev container/codespaces/gitpod). If you need to update your developing setup, for example because it doesn't work
anymore, you will need to copy the relevant files from the [GameSkeleton](https://github.com/hhu-adam/GameSkeleton) template into your game repo.

The relevant files are:

```
.devcontainer/
.docker/
.github/
.gitpod/
.vscode/
lakefile.lean
```

simply copy them from the `GameSkeleton` into your game and proceed as above,
i.e. `lake update -R && lake build`.

(Note: You should not need to modify any of these files, with the exception of the `lakefile.lean`,
where you need to add any dependencies of your game, or remove mathlib if you don't need it.)
