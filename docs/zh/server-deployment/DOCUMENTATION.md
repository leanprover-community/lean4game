# 服务器

服务器由两个部分组成，名为"relay"和"server"。

前者"relay"是设置与客户端的套接字连接、启动 lean 服务器处理文件并在 lean 服务器和客户端之间中继消息的服务器。`index.mjs` 是需要运行的文件，例如使用 `pm2` 或调用 `npm run start:server` 或 `npm run production`，稍后会详细介绍。

后者"server"是 lean 服务器，有两个工作。首先，它产生"gameserver"可执行文件，这是处理玩家游玩文件的 lean 服务器。第二个工作是提供创建游戏时使用的 lean 命令。这些位于 `Commands.lean` 中。

## 集成到游戏中

游戏需要"server"作为 lake 依赖项，这在游戏的 lakefile 中完成。

游戏导入 `GameServer`，它提供创建游戏所需的所有 API。

特别是 lean 命令 `MakeGame` 编译整个游戏。静态信息作为 JSON 文件存储在 `.lake/gamedata` 中以便更快加载，而其他数据仅保存到 lean env-extensions 中，lean 服务器在加载 lean 文件后可以访问这些数据。

为了成功运行游戏，重要的是游戏的 `.lake` 文件夹内的"gameserver"可执行文件实际上已构建。
目前，这通过在调用 `lake update -R`（在游戏文件夹中）时的 lake-post-update-hook 发生，但如果失败，您总是可以通过调用 `lake build gameserver` 手动构建它。
（两个命令都要在游戏目录中执行！）

## 修改服务器

### 启动服务器

当使用[手动安装](../getting-started/running_locally.md#manual-installation)时，您可以使用以下命令运行服务器

```
npm start
```

这样，对 `client/` 或 `relay/` 中文件的任何更改都会导致服务器自动重启。

或者，您可以运行 `npm run build` 然后运行命令

```
npm run start:client
npm run production
```

（在两个单独的终端中）来测试服务器的生产模式。这样它只会在您构建和重启服务器时更改。

### 修改 lean 服务器

要测试修改的 lean 服务器（即 `server/` 的内容），您可以使用本地开发设置并在您的游戏中调用 `lake update -R -Klean4game.local`，然后调用 `lake build`。
这将导致 lake 寻找本地 lean 服务器作为依赖项，而不是从 git 下载的版本。

您可以在 https://localhost:3000/#/g/local/{FolderName} 玩本地游戏，其中您将 `{FolderName}` 替换为游戏文件夹名称。

在 `server/` 中修改后，您需要调用 `lake build gameserver`（在 `server/` 或游戏文件夹中调用）来重建 gameserver 可执行文件，并调用 `lake build`（在游戏文件夹中调用）来重建游戏。
