import NNG.Levels.Power.Level_8

Game "NNG"
World "Power"
Title "Power World"

Introduction
"
A new world with seven levels. And a new import!
This import gives you the power to make powers of your
natural numbers. It is defined by recursion, just like addition and multiplication.
Here are the two new axioms:

  * `pow_zero (a : ℕ) : a ^ 0 = 1`
  * `pow_succ (a b : ℕ) : a ^ succ b = a ^ b * a`

The power function has various relations to addition and multiplication.
If you have gone through levels 1--6 of addition world and levels 1--9 of
multiplication world, you should have no trouble with this world:
The usual tactics `induction`, `rw` and `rfl` should see you through.
You should probably look at your inverntory again: addition and multiplication
have a solid API by now, i.e. if you need something about addition
or multiplication, it's probably already in the library we have built.
Collectibles are indication that we are proving the right things.

The levels in this world were designed by Sian Carey, a UROP student
at Imperial College London, funded by a Mary Lister McCammon Fellowship,
in the summer of 2019. Thanks Sian!
"