# 服务器维护者注意事项

为了设置服务器以允许导入，需要创建一个
[Github 访问令牌](https://docs.github.com/en/authentication/keeping-your-account-and-data-secure/managing-your-personal-access-tokens)。一个仅具有公共仓库读取权限的细粒度访问令牌就足够了。

您需要设置环境变量 `LEAN4GAME_GITHUB_USER` 和 `LEAN4GAME_GITHUB_TOKEN`，包含您的用户名和访问令牌。例如，如果您使用 `pm2`，可以在 `ecosystem.config.cjs` 中设置这些。

然后人们可以调用：

> https://{website}/import/trigger/{owner}/{repo}

其中您需要替换：
- website：您的服务器运行的网站，例如 `localhost:3000`
- owner, repo：您想从 github 加载的游戏的所有者和仓库名称。

这将触发从 github 下载您游戏的最新版本到您的服务器。一旦此导入报告"Done"，您应该能够在以下位置玩您的游戏：

> https://{website}/#/g/{owner}/{repo}

## 数据管理
所有下载的内容都保留在文件夹 `lean4game/games` 中。子文件夹 `tmp` 包含下载的工件，可以放心删除。其他文件夹应该只包含构建的 lean 游戏，按所有者和仓库排序。

## 服务器容量

如果您想在首页显示服务器容量，您可以创建一个形式如下的文件 `lean4game/games/stats.csv`：

```
CPU,MEM
0.1,0.8
```

这些数字将显示在首页（"CPU: 10 % used" 和 "RAM: 80 % used"）。

如果您只想要其中一个数字，请将您不想要的数字替换为 `nan`（或任何其他不能解析为数字的内容）。

如果您不想显示任何一个，只需不创建 `stats.csv`

使用您自己的脚本或 cronjob 根据需要更新 CSV 文件。
