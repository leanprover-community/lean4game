# 创建新游戏

本教程将指导您为 lean4 创建新游戏。内容涵盖从编写新关卡、本地测试游戏到在线发布游戏的全过程。

## 1. 创建项目

1. 使用 [GameSkeleton 模板](https://github.com/hhu-adam/GameSkeleton) 为您的游戏创建新的 github 仓库：在 github 上，点击 "Use this template" > "Create a new repository"。
2. 克隆游戏仓库。
3. 运行 `lake update -R && lake build` 来构建 Lean 项目。

### 运行游戏

现在您可以在 VSCode 中打开游戏（`cd YourGame/` 然后 `code .`），并像常规 Lean 项目一样开始修改它。要运行游戏，请参考下面的"**6. 本地测试游戏**"部分。

## 2. Game.lean

文件 `Game.lean` 是游戏的骨干，将所有内容整合在一起。

1. `MakeGame`：这个命令是游戏构建的地方。如果有需要修复的问题，它们将在这里显示为警告或错误（VSCode 中的橙色/红色波浪线）。注意您可能需要调用 "Lean: Restart File"（Ctrl+Shift+X）来重新加载文件并查看在其他文件中所做的更改。
1. `Title`：设置游戏的显示标题。
1. `Introduction`：这是在世界选择树旁边开始时显示的文本。
1. `Info`：这将在游戏菜单中显示为"游戏信息"。用它来显示制作人员、资助和其他关于游戏的元信息。
1. 导入：文件需要导入所有世界文件，我们稍后会看到。如果您添加新世界，记得在这里导入它！
1. `Dependency`：（可选）这个命令在世界树中添加另一条边。游戏会根据使用的策略/定理自动计算它们。但是，有时您需要游戏无法计算的依赖关系，例如您在一个世界中解释了 `≠`，而在另一个世界中，用户应该已经知道它。语法是 `Dependency World₁ → World₂ → World₃`。

所以 `Game.lean` 具有以下结构：

```lean
import GameServer

-- 导入所有世界
import Game.Levels.Tutorial

Title "我的游戏"

Introduction "
嗨，很高兴您来到这里！点击一个世界开始。
"

Info "
这个游戏由我开发。
"

-- Dependency World₁ → World₂ -- 因为 `≠`

MakeGame
```

### 局部记号

**重要**：如果您在游戏中使用任何局部记号，您需要在 `MakeGame` 之前手动打开这些命名空间，以便在清单中看到记号。

例如（使用 mathlib），写

```
open BigOperators

MakeGame
```

以便看到 `∑ x in s, f x` 而不是 `Finset.sum s fun x => f x`。

## 3. 创建关卡

在本教程中，我们首先学习关卡。游戏由世界树组成，每个世界有若干关卡，编号从 1 到 n。这里我们创建世界 `MyWorld` 的第 1 关。我们在下一节将这个世界添加到游戏中。

最小的关卡文件如下所示。有许多选项可以添加，我们将在后面的部分深入探讨

```lean
import GameServer

World "MyWorld"
Level 1
Title "Hello World"

Introduction "
在关卡开始时显示的消息。用它来解释任何新概念。
"

/-- 使用 latex 的自然语言练习陈述：$\iff$。 -/
Statement (n : Nat) : 0 + n = n := by
  sorry

Conclusion "
关卡完成时显示的消息
"
```

1. 创建文件夹 `Game/Levels/MyWorld`
1. 创建文件 `Game/Levels/MyWorld/L01_hello.lean`
1. 将上述内容复制到您的第一个关卡中。

## 4. 创建世界

现在我们创建一个世界。为此，我们创建一个文件 `MyWorld.lean`，它导入这个世界的所有关卡：

```lean
import Game.Levels.MyWorld.L01_hello

World "MyWorld"
Title "我的第一个世界"

Introduction
"
这个介绍文本在首次进入世界时显示。
"
```

1. 创建文件 `Game/Levels/MyWorld.lean`
1. 使用上面的模板，确保您导入这个世界的所有关卡。
1. 在 `Game.lean` 中用 `import Game.Levels.MyWorld` 导入世界

现在您创建了一个有一个关卡的世界并添加了它🎉 `Game.lean` 中的命令 `MakeGame` 会显示您可能需要修复的任何问题。目前，它显示

```text
No world introducing sorry, but required by MyWorld
```

这意味着世界 `MyWorld` 在证明中使用了策略 `sorry`，但 `sorry` 还没有在任何地方被介绍。

## 5. 重构现有世界

[GameSkeleton 模板](https://github.com/hhu-adam/GameSkeleton) 包含一个 bash 脚本 `sofi.sh`
（`s`ort `o`ut `f`ilenames and `i`mports），
它可以帮助重构现有世界，例如如果您想重新排序或重命名现有关卡，或在中间添加额外的关卡。例如，假设您在文件夹中有一个"算术世界"

    Game/Levels/Arithmetic

由下表左列中列出的三个关卡组成。假设您想切换乘法和加法的顺序，并在中间插入一个关于减法的额外关卡。然后您可以简单地编辑*文件名*如第二列所示，并为减法关卡添加额外的文件，使文件按字母顺序排序时处于预期的顺序（如第三列所示）。

| 现有关卡           | 手动更改                 | 按字母顺序排列的文件        | 最终结果            |
|--------------------|--------------------------|-----------------------------|---------------------|
| L01\_hello.lean    | L01\_hello.lean          | L01\_hello.lean             | L01\_hello.lean     |
| L02\_multiply.lean | **L03**\_multiply.lean   | L02a\_add.lean              | L02\_add.lean       |
| L03\_add.lean      | **L02a**\_add.lean       | L02b\_substract.lean        | L03\_substract.lean |
|                    | **L02b\_substract.lean** | L03\_multiply.lean          | L04\_multiply.lean  |

调用

    ./sofi.sh Game/Levels/Arithmetic

然后将

- 重命名文件如最后一列所示，
- 更新每个文件中的关卡编号，
- 合理地尝试更新每个关卡文件中的 `import` 语句，以及
- 更新基础文件 `Game/Levels/Arithmetic.lean` 中的导入。

更多详细信息记录在脚本本身中。

最后不要忘记用以下命令将所有新/重命名的文件添加到 git：

    git add Game/Levels/Arithmetic/

## 6. 本地测试游戏

现在是时候本地测试游戏并玩它了。

有多种方法可以在本地启动游戏进行测试，详见[如何本地运行游戏](../getting-started/running_locally.md)。如果您在设置任何一种方法时遇到问题，请联系我们！

## 7. 深入关卡创建

现在您有了一个运行的游戏，我们更仔细地看看关卡文件以及您设计游戏的所有选项。

### 7. a) 清单

玩家有一个包含策略、定理和定义的清单，这些在游戏过程中解锁。您可以通过在 `Statement` 下面添加以下内容之一来在关卡中解锁/介绍这些项目。

```lean
NewTactic induction simp
NewTheorem Nat.zero_mul
NewDefinition Pow
```

**重要：** 本节 6a) 中的所有命令都期望它们作为输入的 `Name` 是**完全限定的**。例如 `NewTheorem Nat.zero_mul` 而不是 `NewTheorem zero_mul`。

#### 文档条目

您会看到关于缺少定理文档的警告。您可以通过在它上面某处添加如下的文档条目来修复它。

```lean
/--
一些描述
-/
TheoremDoc Nat.zero_mul as "zero_mul" in "Mul"

/--
一些描述
-/
TacticDoc simp

/--
一些描述
-/
DefinitionDoc Pow as "^"
```

（例如，您也可以创建文件 `Game/Doc/MyTheorems.lean`，在那里添加您的文档并导入它）

如果您不为清单提供任何内容，游戏将尝试找到该项目的文档字符串并显示该文档字符串。

#### 清单管理

您有几个选项来禁用在之前关卡中已解锁的清单项目：

```lean
DisabledTactic, DisabledTheorem, OnlyTactic, OnlyTheorem
```

具有与上面相同的语法。前两个为此关卡禁用项目，后两个禁用除指定项目之外的所有项目。

#### 定理标签

定理被分类到标签中。用 `TheoremTab "Mul"` 您指定在此关卡中默认应该打开哪个标签。

#### 隐藏策略

`NewHiddenTactic` 让您添加策略而不将其添加到清单中。这对策略的变体很有用。例如，您可以这样做

```lean
NewTactic rw
NewHiddenTactic rewrite nth_rewrite rwa
```

只有 `rw` 会出现在清单中。

### 7. b) 陈述

陈述是关卡的练习。基础工作与在 `example` 或 `theorem` 中的工作相同。但是请注意，您**必须**进行策略证明，即 `:= by` 是语法的硬编码部分

#### 名称

您可以给您的练习一个名称：`Statement my_first_exercise (n : Nat) …`。如果您这样做，它将被添加到清单中并在未来的关卡中可用。
您可以像使用 `theorem` 一样将 `Statement` 放在命名空间内。

#### 文档字符串 / 练习陈述

添加包含自然语言练习陈述的文档字符串。如果您这样做，它将出现在练习的顶部。有关格式的更多详细信息，请参见[游戏中的 LaTeX](../game-development/latex.md)。

```lean
/-- 使用 latex 的自然语言练习陈述：$\iff$。 -/
Statement ...
  sorry
```

有关更多详细信息和功能，请阅读[编写练习](../game-development/writing_exercises.md)

### 7. c) 证明

证明必须始终是策略证明，即 `:= by` 是语法的强制部分。

有一些额外的策略可以帮助您构建证明：

- `Hint`：您可以使用 `Hint "text"` 在游戏中的目标状态与放置 `Hint` 的位置匹配时显示文本。有关提示的更多选项，请参见下文。
- `Branch`：在证明中您可以添加运行替代策略序列的 `Branch`，这有助于在不同位置设置 `Hints`。`Branch` 不影响主证明，不需要完成任何目标。
- `Template`/`Hole`：用于提供示例证明模板。`Template` 内的任何内容都将被复制到编辑器中，所有 `Hole` 都被替换为 `sorry`。注意，拥有 `Template` 将强制用户为此关卡使用编辑器模式。

要记住的一点是，游戏将查看主证明来确定需要哪些策略和定理，但它忽略任何 `Branch`。

### 7. d) 提示

对于游戏开发来说，最重要的可能是 `Hints`。

每当玩家的当前目标与提示在示例证明中放置的目标匹配时，提示就会显示。您可以使用 `Branch` 在死胡同或替代证明分支中放置提示。

阅读[更多关于提示](../game-development/hints.md)了解它们如何工作以及有哪些选项。

### 7. e) 额外：图像
您可以在游戏的任何层级（即游戏/世界/关卡）添加图像。这些将在您的游戏中显示。

图像需要放在 `images/` 中，您需要在 2)、3) 或 4) 中创建的文件之一（即游戏/世界/关卡）中添加像 `Image "images/path/to/myWorldImage.png"` 这样的命令。

注意：目前，只显示世界的图像。它们出现在世界的介绍中。

您也可以在文本中嵌入图像，如[Markdown](../game-development/markdown.md)中所述。

## 8. 更新您的游戏

原则上，更新您的游戏到新的 Lean 版本就像修改 `lean-toolchain` 一样简单。但是，您应该阅读[更新现有游戏](../getting-started/update_game.md)中的详细信息。

## 9. 添加翻译

参见[翻译游戏](../game-development/translate.md)。

## 10. 发布您的游戏

要在官方服务器上发布您的游戏，请参见[发布游戏](../getting-started/publish_game.md)

在 `MakeGame` 命令之前，您可以在 `Game.lean` 中添加一些更多选项，这些选项描述在服务器登录页面上可见的磁贴：

```lean
Languages "English"
CaptionShort "游戏模板"
CaptionLong "您应该使用这个游戏作为您自己游戏的模板并添加您自己的关卡。"
Prerequisites "NNG"
CoverImage "images/cover.png"
```
* `Languages`：目前只有一种语言（大写英文名称）。磁贴将显示相应的旗帜。
* `CaptionShort`：一个标语。出现在图像上方。
* `CaptionLong`：2-4 句话来描述游戏。
* `Prerequisites` 您在玩这个游戏之前应该玩的其他游戏列表，例如 `Prerequisites "NNG" "STG"`。游戏名称是自由文本。
* `CoverImage`：您可以创建文件夹 `images/` 并在那里放置游戏使用的图像。最大比例约为 500x200（宽 x 高），但在窄屏幕上可能会水平裁剪。

## 11. 高级主题

### 自定义游戏 UI

有一些选项可以自定义游戏内容的显示方式。这些可以使用 `Game.lean` 内的以下命令进行配置

```
Settings
  (unbundleHyps := true)
  (anotherOption := false)
```

目前存在的选项有：

* `unbundleHyps`（默认：`false`）：如果启用，显示两行 `A : Prop` 和 `B : Prop` 而不是单行 `A B : Prop`。

### Markdown

文本通常应该支持 markdown。有关如何使用 markdown 的一些提示，请参见
[Markdown 样式](../game-development/markdown.md)。

特别是，您可以在文本中嵌入图像，请参见该文件中的具体说明。

### 转义

在字符串内，您需要转义反斜杠，但在文档字符串内不需要，因此您会写 `Introduction "这里有一些 latex：$\\iff$。"` 但
  `/-- 这里有一些 latex：$\iff$。 -/ Statement ...`

### LaTeX 支持

LaTeX 使用 [KaTeX 库](https://katex.org/) 渲染，
有关详细信息，请参见[在游戏中使用 LaTeX](../game-development/latex.md)。

### 关卡数量限制

超过 16 个关卡的世界将显示为关卡向外螺旋，
最好保持在该界限以下。超过 22 个关卡，螺旋开始失控。
