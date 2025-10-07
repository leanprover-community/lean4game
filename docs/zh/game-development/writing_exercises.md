# 编写练习

本页面更详细地介绍 `Statement` 命令以及您编写更好练习/关卡的所有选项。

## 描述性文本
您可以编写一些在策略模式下出现在证明状态上方的文本：
```
/-- 一些描述性文本 -/
Statement my_statement ...
```

## 局部 `let` 定义
如果您想创建一个仅对此练习有效的局部定义/记号（例如函数 `f : ℤ → ℤ := fun x ↦ 2 * x`），推荐的方法是使用 `let` 语句：

```lean
Statement (a : ℤ) (h : 0 < a) :
    let f : ℤ → ℤ := fun x ↦ 2 * x
    0 < f a := by
  sorry
```

游戏会自动 `intros` 这样的 `let` 语句，这样您和玩家将看到以下初始证明状态：

```
a: ℤ
h: 0 < a
f: ℤ → ℤ := fun x => 2 * x
⊢ 0 < f a
```

## "前言" 和非 `Prop` 值练习

您可以使用以下语法 `(preamble := tac)`，其中 `tac` 是策略序列。

```
Statement my_statement (preamble := dsimp) (a : ℤ) (h : 0 < a) :
    0 < f a := by
  sorry
```

这个策略序列将在练习交给玩家之前执行。

例如，如果您的练习是构造一个结构，您可以使用 `preamble` 正确填充所有数据字段，将结构的所有 `Prop` 值字段作为单独的目标留给玩家证明。

注意：`(preamble := tac)` 总是必须写在可选名称和第一个假设之间。尽管如此，您可以在策略序列中使用所有假设，因为它只在证明开始时评估。

## 属性

您可以像对 `theorem` 一样添加属性。最值得注意的是，您可以使您的命名练习成为 `simp` 定理：

```lean
@[simp]
Statement my_simp_theorem ...
```

## 格式化

您可以在引号内使用 markdown 进行格式化，如 `Hint ""`。也支持 Latex，请参见 latex.md。

## 将命名语句添加为定理
可以这样做：
```
Statement my_statement ...

NewTheorem my_statement
```
要在未来的关卡中使用 `my_statement`，您必须导入引入 `my_statement` 的关卡。
`my_statement` 甚至在完成关卡之前就可以使用，但游戏足够智能，不允许您使用它来轻易解决关卡。它在关卡后可用，但确实作为定理出现在您的清单中。

您也可以避免使用命名语句，只创建一个普通的 `theorem` 并在下一关卡中使用 `NewTheorem`。
