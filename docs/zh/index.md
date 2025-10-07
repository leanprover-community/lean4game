# Lean 4 Game

这是托管在 [adam.math.hhu.de](https://adam.math.hhu.de) 的 Lean 游戏平台的源代码。

## 创建游戏

请按照教程 [创建游戏](game-development/create_game.md) 进行操作。特别地，这几个步骤您可能会感兴趣：

* 步骤 6：[如何在本地运行游戏](getting-started/running_locally.md)
* 步骤 8：[如何更新现有游戏](getting-started/update_game.md)
* 步骤 10：[如何发布游戏](getting-started/publish_game.md)
* [故障排除](getting-started/troubleshoot.md)

## 文档

本文档仍在更新中，但这里链接的文档应该是最新的：

### 游戏创建 API

- [创建游戏](game-development/create_game.md)：**主要参考文档**。
- [更多关于提示的信息](game-development/hints.md)：描述 `Hint` 和 `Branch` 策略。

### 前端 API

* [如何在本地运行游戏](getting-started/running_locally.md)：在您的计算机上玩游戏
* [如何更新现有游戏](getting-started/update_game.md)：更新到新的 lean 版本
* [如何发布游戏](getting-started/publish_game.md)：将您的游戏加载到 adam.math.hhu.de 供其他人玩

### 后端

尚未完全编写。

* [服务器](server-deployment/DOCUMENTATION.md)：描述服务器部分（即 `server/` 和 `relay/` 的内容）。

## 贡献

欢迎对 `lean4game` 做出贡献！

### 翻译

游戏支持翻译成各种语言。如果要添加翻译，需执行以下操作：

1. 在 `client/src/config.json` 中，添加您的新语言。"iso" 键是 ISO 语言代码，取值为 "i18next" 或 "GNU gettext"；"flag" 键应该符合 [react-country-flag](https://www.npmjs.com/package/react-country-flag) 的格式。
2. 运行 `npm run translate`。这将创建一个新文件 `client/public/locales/{language}/translation.json`。（或者您可以复制粘贴 `client/public/locales/en/translation.json`）
3. 添加所有翻译内容。
4. 提交您对 `config.json` 所做的更改以及新的 `translation.json`。

有关翻译游戏，请参阅 [翻译游戏](game-development/translate.md)。

## 安全性

为用户提供对服务器上运行的 Lean 实例的访问是一个严重的安全风险。这就是为什么我们使用 bubblewrap 启动 Lean 服务器的原因。

## 联系方式

如果在使用 ```adam.math.hhu.de``` 时遇到技术问题，请通过 <a href="mailto:matvey.lorkish@hhu.de?subject=Lean4Game: <Your%20Question>">电子邮件</a> 联系我们。

## 致谢

该项目主要由 Alexander Bentkamp 和 Jon Eugster 开发。

它基于 [Lean Game Maker](https://github.com/mpedramfar/Lean-game-maker) 和 [Natural Number Game (NNG)](https://www.ma.imperial.ac.uk/~buzzard/xena/natural_number_game/) 的想法，后者由 Kevin Buzzard 和 Mohammad Pedramfar 开发，以及 Patrick Massot 的原型：[NNG4](https://github.com/PatrickMassot/NNG4)。
