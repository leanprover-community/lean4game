# Refactor a Game

## Refactoring an existing world

The [GameSkeleton template](https://github.com/hhu-adam/GameSkeleton) contains a bash script `sofi.sh`
(`s`ort `o`ut `f`ilnames and `i`mports),
which can help restructure existing worlds, for example if you want to reorder or rename existing levels,
or add additional levels in the middle. Say, for example, you have an “Arithmetic World” in the
folder

    Game/Levels/Arithmetic

consisting of the three levels listed in the leftmost column of the table below. Suppose you want to
switch the order of multiplication and addition, and insert an additional level on subtraction in
between. Then you can simply edit the _file names_ as in the second column, and add the additional
file for the level on substraction, so that the files are in the intended order when sorted
alphabetically (as displayed in the third column).

| existing levels    | manual changes           | files in alphabetical order | end result          |
| ------------------ | ------------------------ | --------------------------- | ------------------- |
| L01\_hello.lean    | L01\_hello.lean          | L01\_hello.lean             | L01\_hello.lean     |
| L02\_multiply.lean | **L03**\_multiply.lean   | L02a\_add.lean              | L02\_add.lean       |
| L03\_add.lean      | **L02a**\_add.lean       | L02b\_substract.lean        | L03\_substract.lean |
|                    | **L02b\_substract.lean** | L03\_multiply.lean          | L04\_multiply.lean  |

Calling

    ./sofi.sh Game/Levels/Arithmetic

will then

- rename the files as in the last column,
- update the level number in each file,
- make a reasonable attempt to update the `import` statements in each of the
  level files, and
- update the imports in the base file `Game/Levels/Arithmetic.lean`.

More details are documented in the script itself.

Don't forget to add all your new/renamed files to git with

    git add Game/Levels/Arithmetic/

at the end.
