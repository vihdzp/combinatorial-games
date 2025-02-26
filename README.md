# Combinatorial games in Lean

A formalization of topics within combinatorial game theory in Lean 4.

## What is it?

A combinatorial game is two-player terminating game with perfect information. In other words, two players (called Left and Right) alternate changing some game state, which they always have full knowledge of. The game cannot go on forever, and whoever is left without a move to make loses.

Examples of combinatorial games include [Tic-Tac-Toe](https://en.wikipedia.org/wiki/Tic-tac-toe),
[Chess](https://en.wikipedia.org/wiki/Chess), and [Nim](https://en.wikipedia.org/wiki/Nim). Counterexamples include [poker](https://en.wikipedia.org/wiki/Poker), or the [Gale–Stewart games](https://en.wikipedia.org/wiki/Borel_determinacy_theorem#Gale%E2%80%93Stewart_games) within Borel determinacy (see however [this repo](https://github.com/sven-manthe/A-formalization-of-Borel-determinacy-in-Lean) for more info on them).

## What's in scope?

There are broadly four things this repository aims to formalize:

- The theory of [general combinatorial games](https://github.com/users/vihdzp/projects/3) (temperature, dominated positions, reversible positions, etc.)
- The theory of [specific combinatorial games](https://github.com/users/vihdzp/projects/7) (poset games, Hackenbush, tic-tac-toe, etc.)
- The theory of [nimbers](https://github.com/users/vihdzp/projects/8) (prove their algebraic completeness, prove the simplicity theorems)
- The theory of [surreal numbers](https://github.com/users/vihdzp/projects/9) (set up their field structure, prove their representations as Hahn series)

## References

Our development of combinatorial game theory is based largely on Conway (2001), supplemented by various other more modern resources.

* Conway, J. H. - On numbers and games (2001)
* Dierk Schleicher and Michael Stoll - [An Introduction to Conway's Games and Numbers](https://arxiv.org/abs/math/0410026) (2005)
* Siegel, A. N. - Combinatorial game theory (2013)