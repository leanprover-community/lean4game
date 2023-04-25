import NNG.Metadata
import NNG.MyNat.Definition

Game "NNG"
World "Tutorial"
Level 3
Title "Peano axioms"

open MyNat

Introduction
"
Now we start from the beginning, where we don't know about addition or multiplication on `ℕ`.

All we get is the following data:

* a term `(0 : ℕ)`, interpreted as the zero number.
* a function `succ : ℕ → ℕ`, with `succ n` interpreted as \"the number after $n$\".
* the principle of mathematical induction.

These axioms are essentially the axioms isolated by Peano which uniquely characterise the natural
numbers (we also need recursion, but we can ignore it for now).
The first axiom says that $0$ is a natural number.
The second says that there is a $\\operatorname{succ}$ function which eats a number and spits out
the number after it, so $\\operatorname{succ}(0)=1$, $\\operatorname{succ}(1)=2$ and so on.

Peano's last axiom is the principle of mathematical induction. This is a deeper fact.
It says that if we have infinitely many true/false statements $P(0)$, $P(1)$, $P(2)$ and so on,
and if $P(0)$ is true, and if for every natural number $d$ we know that $P(d)$ implies
$P(\\operatorname{succ}(d))$, then $P(n)$ must be true for every natural number $n$.
It's like saying that if you have a long line of dominoes, and if you knock the first
one down, and if you know that if a domino falls down then the one after it will fall
down too, then you can deduce that all the dominos will fall down. One can also think
of it as saying that every natural number can be built by starting at $0$ and then applying
$\\operatorname{succ}$ a finite number of times.

Peano's insights were firstly that these axioms completely characterise the natural numbers,
and secondly that these axioms alone can be used to build a whole bunch of other structure
on the natural numbers, for example addition, multiplication and so on.

This game is all about seeing how far these axioms of Peano can take us.

Now let us practise the use of `rw` with this new function `succ`:
"

Statement
"If $\\operatorname{succ}(a) = b$, then $\\operatorname{succ}(\\operatorname{succ}(a)) = \\operatorname{succ}(a)$."
    (a b : ℕ) (h : (succ a) = b) : succ (succ a) = succ b := by
  Hint "You can use `rw` and your assumption `{h}` to substitute `succ a` with `b`.

  Notes:

  1) We do not need brackets for function application the way we would write
  them in mathematics: `succ b` means $\\operatorname\{succ}(b)$.
  2) If you would want to substitute instead `b` with `succ a`, you can do that
  writing a small `←` (`\\l`, i.e. backslash + small letter L + space)
  before `h` like this: `rw [← h]`."
  Branch
    simp? -- TODO: `simp` should not make progress.
  Branch
    rw [← h]
    Hint (hidden := true) "Now both sides are identical…"
  rw [h]
  Hint (hidden := true) "Now both sides are identical…"
  rfl

Conclusion
"
You may also be wondering why we keep writing `succ b` instead of `b + 1`.
This is because we haven't defined addition yet!
On the next level, the final level of Tutorial World,
we will introduce addition, and then we'll be ready to enter Addition World.
"
