There are multiple ways how to format the text content of your game. Notably Markdown with KaTeX.

# Escaping
Generally, if you add text inside quotes `" "` (e.g. in `Hint`) you need to escape
backslashes, but if you provide text inside a doc comment
`/-- -/` (e.g. in the `Statement` description) you do not!

This means for example you'd write `/-- $\iff$ -/` but `"$\\iff$"`.

Furthermore, inside `Hint` you need to escape all opening curly brackets as `\{` since `{h}` is syntax for inserting a variable name `h`.

# Images


# KaTeX

LaTeX syntax is provided trough the [KaTeX library](https://katex.org). KateX supports most but not all of latex and its packages.
See [supported](https://katex.org/docs/supported.html).

## Examples

### Commutative diagrams

Here is an example of how to write a commutative diagram in KaTeX:

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

Again, note that inside a string like `Hint`/`Introduction`/`Conclusion`/etc. you need to escape `\` and potentially `{`.

E.g. `\begin` as `\\begin`, `\\` as `\\\\` and inside a
`Hint`, `@>{f}>>` as `@>\{f}>>`.

See https://www.jmilne.org/not/Mamscd.pdf

### Truth Tables

KaTeX does not support the tabular environment. You can use the array environment instead.

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
