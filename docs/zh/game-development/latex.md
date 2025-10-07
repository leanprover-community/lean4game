有多种方式可以格式化您游戏的文本内容。特别是使用 KaTeX 的 Markdown。

# 转义
通常，如果您在引号 `" "` 内添加文本（例如在 `Hint` 中），您需要转义反斜杠，但如果您在文档注释 `/-- -/` 内提供文本（例如在 `Statement` 描述中），则不需要！

这意味着例如您会写 `"$\\iff$"` 而不是 `/-- $\iff$ -/`。

此外，在 `Hint` 内您需要将所有开放的大括号转义为 `\{`，因为 `{h}` 是插入变量名 `h` 的语法。

# KaTeX

LaTeX 语法通过 [KaTeX 库](https://katex.org) 提供。KateX 支持大部分但不是全部的 latex 及其包。
参见[支持的功能](https://katex.org/docs/supported.html)。

## 示例

### 交换图

以下是如何在 KaTeX 中编写交换图的示例：

$$
\begin{CD}
      A  @>{f}>> B @<{g}<< C    \\
  @V{h}VV    @V{i}VV   @V{j}VV \\
      D  @<{k}<< E @>{l}>> F    \\
  @A{m}AA    @A{n}AA   @V{p}VV \\
      G  @<{q}<< H @>{r}>> I
\end{CD}
$$

```
$$
\begin{CD}
      A  @>{f}>> B @<{g}<< C    \\
  @V{h}VV    @V{i}VV   @V{j}VV \\
      D  @<{k}<< E @>{l}>> F    \\
  @A{m}AA    @A{n}AA   @V{p}VV \\
      G  @<{q}<< H @>{r}>> I
\end{CD}
$$
```

再次注意，在像 `Hint`/`Introduction`/`Conclusion`/等字符串内，您需要转义 `\` 和可能的 `{`。

例如 `\begin` 作为 `\\begin`，`\\` 作为 `\\\\`，在 `Hint` 内，`@>{f}>>` 作为 `@>\{f}>>`。

参见 https://www.jmilne.org/not/Mamscd.pdf

### 真值表

KaTeX 不支持 tabular 环境。您可以使用 array 环境代替。

$$
\begin{array}{|c|c|}
  \hline
  P & ¬P \\
  \hline
  T & F  \\
  F & T  \\
  \hline
\end{array}
$$

```
$$
\begin{array}{|c|c|}
  \hline
  P & ¬P \\
  \hline
  T & F  \\
  F & T  \\
  \hline
\end{array}
$$
```
