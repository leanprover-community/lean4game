# Escaping
Generally, if you add text inside quotes `" "` (e.g. in `Hint`) you need to escape
backslashes, but if you provide text inside a doc comment
`/-- -/` (e.g. in the `Statement` description) you do not!

Furthermore, inside `Hint` you need to escape all opening curly brackets as `\{` since `{h}` is syntax for inserting a variable name `h`.

## Example
Inside strings, you need to escape backslashes, but not inside doc-strings, therefore you
  would write `Introduction "some latex here: $\\iff$."` ,  but
  `/-- some latex here: $\iff$. -/ Statement ...`

# Support
It is important to mention that KateX supports most but not all of latex and its packages.
See [supported](https://katex.org/docs/supported.html).
