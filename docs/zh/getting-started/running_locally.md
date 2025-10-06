# 本地运行游戏

安装说明尚未在 Mac/Windows 上测试。非常欢迎您的意见反馈！

请同时参考[故障排除集合](troubleshoot.md)，其中收集了一些已知的问题。

有几种在本地运行游戏的选项：

1. VSCode 开发容器：需要在您的机器上安装 `docker`
2. Codespaces：需要活跃的互联网连接，计算时间有限
3. Gitpod：目前还不能正常运行（尚未确认？）
4. 手动安装：需要在您的系统上安装 `npm`

推荐的选项是"VSCode 开发容器"，但您可以根据个人喜好选择上述任何选项。

模板游戏 [GameSkeleton](https://github.com/hhu-adam/GameSkeleton) 包含所有相关文件，可以让您的本地设置（开发容器 / gitpod / codespaces）正常工作。如果您需要在已有游戏中开发新改进，您可以从这个仓库复制文件来手动更新。

## VSCode 开发容器

1.  **安装 Docker 和开发容器** *(一次性)*：<br/>
    参见[官方说明](https://code.visualstudio.com/docs/devcontainers/containers#_getting-started)。
    具体来说，这意味着：
    * 如果您还没有安装 docker 引擎：[安装说明](https://docs.docker.com/engine/install/)。
      我在 linux 上遵循了"服务器"说明。
    * 注意在 Linux 上您需要将您的用户添加到 `docker` 组
      ([参见说明](https://docs.docker.com/engine/install/linux-postinstall/)) 并可能需要重启 shell。
    * 在 VSCode 中打开游戏文件夹：`cd NNG4 && code .` 或在 VSCode 中"打开文件夹"
    * 会出现一条消息提示您安装"Dev Containers"扩展（由 Microsoft 提供）。（或者从 VSCode 扩展中安装它）。

2.  **在开发容器中打开项目** *(每次)*：<br/>
    一旦您安装了开发容器扩展，在 VSCode 中（重新）打开您的游戏项目文件夹。会出现一条消息询问您是否"在容器中重新打开"。

    * 第一次启动会花费一些时间，大约 2-15 分钟。第一次启动后，这应该会很快。
    * 构建完成后，您可以在浏览器中打开 http://localhost:3000，这应该会加载游戏。

3.  **编辑文件** *(每次)*：<br/>
    在 VSCode 中编辑一些 Lean 文件后，打开 VSCode 的终端（视图 > 终端）并运行 `lake build`。现在您可以重新加载浏览器以查看更改。

## Codespaces

您可以使用 Github codespaces 来处理您的游戏（点击仓库绿色按钮"Code"，然后"Codespaces"，然后"在 main 上创建 codespace"）。它应该在后台本地运行游戏。您可以在"Ports"下打开它，然后点击"在浏览器中打开"。

注意：您必须等到 npm 正确启动，这可能需要很长时间。

与开发容器一样，在更改任何 lean 文件后，您需要在运行 `lake build`，然后重新加载浏览器。

## Gitpod

TODO：不确定这是否还能工作！

点击 gitpod 链接打开游戏。同样，您需要等到它完全构建完成，然后在您进行更改时在 shell 中输入 `lake build`。

## 手动安装

这会在您的计算机上手动安装 `lean4game`。（这与设置在线服务器的安装方式相同，只是运行命令（即 `npm start`）不同。）

安装 `nvm`：
```bash
curl -o- https://raw.githubusercontent.com/nvm-sh/nvm/v0.39.2/install.sh | bash
```
然后重新打开 bash 并使用 `command -v nvm` 测试它是否可用（应该打印"nvm"）。

现在安装 node：
```bash
nvm install node
```

克隆游戏（例如这里的 `GameSkeleton`）：
```bash
git clone https://github.com/hhu-adam/GameSkeleton.git
# 或者：git clone git@github.com:hhu-adam/GameSkeleton.git
```

下载依赖项并构建游戏：
```bash
cd GameSkeleton
lake update -R
lake build
```

将服务器仓库克隆到游戏同级的目录中：
```bash
cd ..
git clone https://github.com/leanprover-community/lean4game.git
# 或者：git clone git@github.com:leanprover-community/lean4game.git
```
文件夹 `GameSkeleton` 和 `lean4game` 必须在同一个目录中！

在 `lean4game` 中，安装依赖项：
```bash
cd lean4game
npm install
```

运行游戏：
```bash
npm start
```

您应该看到类似这样的消息：
```bash
[server] > lean4-game@0.1.0 start:server
[server] > (cd server && lake build) && (cd relay && cross-env NODE_ENV=development nodemon -e mjs --exec "node ./index.mjs")
[server]
[client]
[client] > lean4-game@0.1.0 start:client
[client] > cross-env NODE_ENV=development vite --host
[client]
[server] [nodemon] 3.0.#
[server] [nodemon] to restart at any time, enter `rs`
[server] [nodemon] watching path(s): *.*
[server] [nodemon] watching extensions: mjs
[server] [nodemon] starting `node ./index.mjs`
[client]
[client]   VITE v4.5.1  ready in \#\#\# ms
[client]
[client]   ➜  Local:   http://localhost:3000/
[client]   ➜  Network: http://###.###.###.##:3000/
[client] [vite-plugin-static-copy] Collected 7 items.
[server] (node:#####) [DEP0040] [server] Listening on 8080
```

这需要一点时间。最终，游戏将在 http://localhost:3000/#/g/local/GameSkeleton 上可用。将 `GameSkeleton` 替换为您本地游戏的文件夹名称。

## 修改 GameServer

当修改游戏引擎本身（特别是 `lean4game/server` 中的内容）时，您可以使用与上述相同的设置（手动安装）通过使用 `lake update -R -Klean4game.local` 来实时测试它：

```bash
cd NNG4
lake update -R -Klean4game.local
lake build
```
这可以让 lake 在本地搜索 `GameServer` 包，而不是使用 github 上的版本。因此，您可以编辑 `../lean4game` 中的本地 `GameServer` 副本，然后 `lake build` 将直接使用这个修改后的副本来构建您的游戏。
