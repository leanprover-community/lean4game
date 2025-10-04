# 如何更新您的游戏

## 新的 Lean 版本

您可以通过简单地编辑游戏仓库中的 `lean-toolchain` 来将游戏更新到任何 Lean 版本，使其包含新的 lean 版本 `leanprover/lean4:v4.X.0`。

在继续之前，请确保[此仓库中存在 `v4.X.0` 标签](https://github.com/leanprover-community/lean4game/tags)。

然后，根据您使用的设置，执行以下操作之一：

* **Dev Container**：重建 VSCode Devcontainer（不使用缓存！）。
* **本地设置**：在您的游戏文件夹中运行以下命令：
  ```
  lake update -R
  lake build
  ```

  * 此外，如果您有服务器 `lean4game` 的本地副本，
    您应该将其更新到匹配的版本。在文件夹 `lean4game/` 中运行以下命令：
    ```
    git fetch
    git checkout {VERSION_TAG}
    npm install
    ```
    其中 `{VERSION_TAG}` 是上面形式为 `v4.X.0` 的标签
* **Gitpod/Codespaces**：创建一个新的

这将把您的游戏（以及您可能使用的 mathlib 版本）更新到新的 lean 版本。

## 最新的开发设置

您的游戏仓库中有一些文件用于开发设置
（dev container/codespaces/gitpod）。如果您需要更新开发设置，例如因为它不再工作，
您需要将相关文件从 [GameSkeleton](https://github.com/hhu-adam/GameSkeleton) 模板复制到您的游戏仓库中。

相关文件是：

```
.devcontainer/
.docker/
.github/
.gitpod/
.vscode/
lakefile.lean
```

只需将它们从 `GameSkeleton` 复制到您的游戏中，然后按上述方式进行，
即 `lake update -R && lake build`。

（注意：您不应该需要修改这些文件中的任何一个，除了 `lakefile.lean`，
您需要在其中添加游戏的任何依赖项，或者如果不需要 mathlib 则删除它。）
