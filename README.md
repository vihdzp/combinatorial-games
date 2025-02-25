# Combinatorial games in Lean

A formalization of topics within combinatorial game theory in Lean 4.

## What is it?

A combinatorial game is two-player terminating game with perfect information. In other words, two players (called Left and Right) alternate changing some game state, which they always have full knowledge of. The game cannot go on forever, and whoever is left without a move to make loses.

Examples of combinatorial games include [Tic-Tac-Toe](https://en.wikipedia.org/wiki/Tic-tac-toe),
[Chess](https://en.wikipedia.org/wiki/Chess), and [Nim](https://en.wikipedia.org/wiki/Nim). Counterexamples include [poker](https://en.wikipedia.org/wiki/Poker), or the [Gale--Stewart games](https://en.wikipedia.org/wiki/Borel_determinacy_theorem#Gale%E2%80%93Stewart_games) within Borel determinacy (see however [this repo](https://github.com/sven-manthe/A-formalization-of-Borel-determinacy-in-Lean) for more info on them).

## What's in scope?

There are broadly four things this repository aims to achieve:

- Formalize the theory of general combinatorial games, 

Our development of combinatorial game theory is based largely on Conway (2001), supplemented by various other more modern resources.