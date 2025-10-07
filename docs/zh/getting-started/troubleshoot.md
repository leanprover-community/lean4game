# 故障排除

以下是用户遇到的一些问题。

- 您可以使用以下命令重置涉及的 lake 项目（即这里的 `server/` 文件夹以及您的[游戏文件夹](https://github.com/hhu-adam/GameSkeleton)）：
  ```
  cd [项目目录]
  rm -rf .lake/
  lake update -R
  lake build
  ```
  如果您遇到与 Lean 或 lake 相关的问题，您应该首先尝试以这种方式重置它。

# VSCode 开发容器
* 如果您没有收到弹出窗口，您可能已经禁用了它们，您可以通过在 vscode 中运行 `remote-containers.showReopenInContainerNotificationReset` 命令来重新启用它。
* 如果启动容器失败，特别是出现消息 `Error: network xyz not found`，您可能通过 shell 从 docker 中删除了一些内容。尝试在 VSCode 中明确删除容器和镜像（左侧，"Docker" 图标）。然后重新打开 vscode 并让它重建容器。（这将再次花费一些时间）
* 在正常工作的开发容器设置中，http://localhost:3000 应该直接重定向您到 http://localhost:3000/#/g/local/game，尝试看看后者是否可访问。

# 手动安装
以下是使用 `npm` 进行本地设置的已知问题/陷阱。

* 如果在您的 mac/linux 系统上设置了 `CDPATH`，它可能会导致 `npm start` 出现问题，导致服务器崩溃或空白屏幕。特别是 `npm start` 将显示
  ```
  [server] sh: line 0: cd: server: No such file or directory
  [server] npm run start:server exited with code 1
  ```
  作为修复，您可能需要删除手动设置的 `CDPATH` 环境变量。

# 发布
关于上传到服务器的错误。

* 您的游戏概览加载了，但服务器在加载关卡时崩溃：请检查您游戏的 github action 是否和 [GameSkeleton 的](https://github.com/hhu-adam/GameSkeleton/blob/main/.github/workflows/build.yml) 雷同，特别是确保有一个关于构建 "`gameserver`-executable" 的步骤。
