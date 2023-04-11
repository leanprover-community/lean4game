import NNG.Levels.Function.Level_1
import NNG.Levels.Function.Level_2
import NNG.Levels.Function.Level_3
import NNG.Levels.Function.Level_4
import NNG.Levels.Function.Level_5
import NNG.Levels.Function.Level_6
import NNG.Levels.Function.Level_7
import NNG.Levels.Function.Level_8
import NNG.Levels.Function.Level_9


Game "NNG"
World "Function"
Title "Function World"

Introduction
"
If you have beaten Addition World, then you have got
quite good at manipulating equalities in Lean using the `rw` tactic.
But there are plenty of levels later on which will require you
to manipulate functions, and `rw` is not the tool for you here.

To manipulate functions effectively, we need to learn about a new collection
of tactics, namely `exact`, `intro`, `have` and `apply`. These tactics
are specially designed for dealing with functions. Of course we are
ultimately interested in using these tactics to prove theorems
about the natural numbers &ndash; but in this
world there is little point in working with specific sets like `mynat`,
everything works for general sets.

So our notation for this level is: $P$, $Q$, $R$ and so on denote general sets,
and $h$, $j$, $k$ and so on denote general
functions between them. What we will learn in this world is how to use functions
in Lean to push elements from set to set. A word of warning &ndash;
even though there's no harm at all in thinking of $P$ being a set and $p$
being an element, you will not see Lean using the notation $p\\in P$, because
internally Lean stores $P$ as a \"Type\" and $p$ as a \"term\", and it uses `p : P`
to mean \"$p$ is a term of type $P$\", Lean's way of expressing the idea that $p$
is an element of the set $P$. You have seen this already &ndash; Lean has
been writing `n : ℕ` to mean that $n$ is a natural number.
"