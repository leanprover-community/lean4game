# 翻译

游戏服务器使用 [lean-i18n](https://github.com/hhu-adam/lean-i18n) 和 [i18next](https://www.npmjs.com/package/i18next) 支持国际化（"i18n"）。

目前预期的工作流程如下：

1. 当您在游戏中调用 `lake build` 时，它应该自动创建模板文件 `.i18n/en/Game.pot`。或者您可以调用 `lake exe i18n --template` 来重新创建它。
2. 使用 [Poedit](https://poedit.net/)（或类似软件）打开文件 `Game.pot`（"t" 代表 "template"）并翻译所有字符串。将您的工作保存为 `.i18n/{language}/Game.po`。
4. 调用 `lake exe i18n --export-json` 创建服务器需要的所有 Json 文件 `.i18n/{language}/Game.json`。
5. 添加您的翻译（即 `.po` 和 `.json`，但不包括 `.mo` 文件）并推送您的结果，然后[发布游戏](../server-deployment/publish_game.md)。

如果您在游戏的"首选项"中选择正确的语言，您应该能看到您的翻译。

## 详细信息（待合并）

对于翻译，代码块（以一个或多个反引号（\`）开头）和 latex 块（以一个或两个 `$` 开头）被占位符 `§n` 替换，您可以在注释中看到这些内容。
此外，单个换行符（`\n`）将从翻译字符串中删除。

这些预处理步骤旨在改善与自动翻译工具的交互。

## 替代方案：避免 .po

注意：此工作流程可能会发生变化，将来服务器可能能够直接读取 `.po` 文件。在那之前，您也可以选择另一种工作流程：

0. 在 `.i18n/config.json` 中添加 `useJson: true`
1. `lake build` 或 `lake exe i18n --template` 现在将创建 Json：`.i18n/en/Game.json`。
2. 将翻译添加到此 Json 的副本中并将其保存为 `.i18n/{language}/Game.json`

## 非英语游戏

对于用英语以外的语言编写的游戏，您应该在 `.i18n/config.json` 中设置正确的源语言（`sourceLang`）。之后，在 `lake build` 时，模板应该出现在所选语言下，并可以如上所述进行翻译（例如翻译成英语）。

注意像 `pomerge` 这样的工具可能很有用：它允许您执行类似以下操作

```
pomerge de-en.po en-fr.po -o de-fr.po
```

例如，您可以首先创建英语翻译，然后让人们将其翻译成他们自己的语言，最后使用 `pomerge` 从源语言到目标语言创建正确的 PO 文件。

## 新语言

服务器有一组可选择的语言。
如果您的游戏已被翻译成不可选择的语言，请[在 lean4game 开启问题](https://github.com/leanprover-community/lean4game/issues)请求这种新语言。
或者，更好的是，创建 PR 将[服务器界面](https://github.com/leanprover-community/lean4game/tree/main/client/public/locales)翻译成那种新语言。

## 审查

由于此仓库（或游戏）的维护者可能不了解大多数语言，
建议您从 Lean 社区中找到任何人来审查您的翻译并在 PR 上留下积极评论。

拥有来自社区的二级审查员的主要目的是防止错误翻译以及冒犯性或不当语言。

一些建议：

1. JSON 文件是从 PO 文件自动生成的，因此可以进行表面审查。
2. 翻译期间应保持格式。虽然代码片段有占位符，但审查员可能会注意标点符号等细节。
3. [POEdit](https://poedit.net/) 是专门为翻译和审查过程设计的绝佳工具！除其他功能外，它允许您专门审查给定范围的句子，例如一次 50-100 句，并允许更容易地分配工作。
