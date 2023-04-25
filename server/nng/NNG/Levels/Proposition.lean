import NNG.Levels.Proposition.Level_1
import NNG.Levels.Proposition.Level_2
import NNG.Levels.Proposition.Level_3
import NNG.Levels.Proposition.Level_4
import NNG.Levels.Proposition.Level_5
import NNG.Levels.Proposition.Level_6
import NNG.Levels.Proposition.Level_7
import NNG.Levels.Proposition.Level_8
import NNG.Levels.Proposition.Level_9 -- `cc` is not ported


Game "NNG"
World "Proposition"
Title "Proposition World"

Introduction
"
A Proposition is a true/false statement, like `2 + 2 = 4` or `2 + 2 = 5`.
Just like we can have concrete sets in Lean like `mynat`, and abstract
sets called things like `X`, we can also have concrete propositions like
`2 + 2 = 5` and abstract propositions called things like `P`.

Mathematicians are very good at conflating a theorem with its proof.
They might say \"now use theorem 12 and we're done\". What they really
mean is \"now use the proof of theorem 12...\" (i.e. the fact that we proved
it already). Particularly problematic is the fact that mathematicians
use the word Proposition to mean \"a relatively straightforward statement
which is true\" and computer scientists use it to mean \"a statement of
arbitrary complexity, which might be true or false\". Computer scientists
are far more careful about distinguishing between a proposition and a proof.
For example: `x + 0 = x` is a proposition, and `add_zero x`
is its proof. The convention we'll use is capital letters for propositions
and small letters for proofs.

In this world you will see the local context in the following kind of state:

```
Objects:
  P : Prop
Assumptions:
  p : P
```

Here `P` is the true/false statement (the statement of proposition), and `p` is its proof.
It's like `P` being the set and `p` being the element. In fact computer scientists
sometimes think about the following analogy: propositions are like sets,
and their proofs are like their elements.
"