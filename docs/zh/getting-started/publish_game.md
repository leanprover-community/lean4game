# 发布游戏

您可以通过几个简单的步骤在官方 [Lean 游戏服务器](https://adam.math.hhu.de) 上发布您的游戏。

## 1. 将游戏上传到 github

首先，您需要将游戏放在公共 Github 仓库中，并确保 github action 已运行。
可以通过在首页看到绿色勾号，或查看"Actions"标签来检查这一点。

## 2. 导入游戏

查看最新 action 日志，其中 "What's Next?" 标签列出的 URL。具体地说，调用形式为

> adam.math.hhu.de/import/trigger/{USER}/{REPOSITORY}

其中 `{USER}` 和 `{REPOSITORY}` 替换为 github 用户和仓库名称。

打开网页应该会看到一个白色屏幕，显示导入更新并最终报告"Done."

## 3. 玩游戏

现在您可以立即在 `adam.math.hhu.de/#/g/{USER}/{REPOSITORY}` 玩游戏！

## 4. 更新

要上传游戏的新版本，每当您想发布更新版本时，您都必须重复步骤 1. 和 2.。

## 5. 主页

将游戏添加到主页由服务器维护者手动完成。如果您希望将游戏添加到主页中，请告诉我们！

例如，您可以[在 Zulip 上联系 Jon](https://leanprover.zulipchat.com/#narrow/dm/385895-Jon-Eugster)。
