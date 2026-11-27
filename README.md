# Combinatorial games in Lean

A formalization of topics within combinatorial game theory in Lean 4.

## What is it?

A combinatorial game is a deterministic perfect information game. In other words, with nothing like dice involved, players alter some game state, which they always know everything about.<br>
Most discussion and literature tends to additionally use a majority of the following restrictions:

- discrete time
- normal play, where the first player(s) unable to move lose(s)
- well-founded (sometimes called loopfree) / short (well-founded and has a finitely wide tree / graph)
- two players
- (strictly) partizan, as opposed to impartial games where players have the same moves

Examples of combinatorial games include [Nim](https://en.wikipedia.org/wiki/Nim), [Hackenbush](https://en.wikipedia.org/wiki/Hackenbush), [Chomp](https://en.wikipedia.org/wiki/Chomp), [Chess](https://en.wikipedia.org/wiki/Chess), which can end in a tie, the [homicidal chauffeur problem](https://en.wikipedia.org/wiki/Homicidal_chauffeur_problem), in which time is continuous, and [Gale–Stewart games](https://en.wikipedia.org/wiki/Borel_determinacy_theorem#Gale%E2%80%93Stewart_games) within Borel determinacy, which go on forever (see however [this repo](https://github.com/sven-manthe/A-formalization-of-Borel-determinacy-in-Lean) for more info on them).<br>
Non-examples include [poker](https://en.wikipedia.org/wiki/Poker), which has chance elements and hidden information, [tetris](https://en.wikipedia.org/wiki/Tetris), which has perfect information but also chance (unless you can predict your device's pseudo-rng), and [battleships](https://en.wikipedia.org/wiki/Battleship_(game)), which is deterministic but has hidden information.

This repo is focused on discrete-time well-founded two-player combinatorial games in normal play.
Chess, the homicidal chauffeur problem and Gale-Stewart games are non-examples of this.

## What's in scope?

There are broadly four things this repository aims to formalize:

- The theory of [general combinatorial games](https://github.com/users/vihdzp/projects/3) (temperature, dominated positions, reversible positions, etc.)
- The theory of [specific combinatorial games](https://github.com/users/vihdzp/projects/7) (poset games, Hackenbush, tic-tac-toe, etc.)
- The theory of [nimbers](https://github.com/users/vihdzp/projects/8) (prove them algebraically closed, prove the simplest extension theorems)
- The theory of [surreal numbers](https://github.com/users/vihdzp/projects/9) (set up their field structure, prove their representations as Hahn series)

## References

Our development of combinatorial game theory is based largely on Conway (1976), supplemented by various other more modern resources.

* Conway, J. H. - On numbers and games (1976)
* Dierk Schleicher and Michael Stoll - [An Introduction to Conway's Games and Numbers](https://arxiv.org/abs/math/0410026) (2005)
* Siegel, A. N. - Combinatorial game theory (2013)
