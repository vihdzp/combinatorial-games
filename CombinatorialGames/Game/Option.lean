/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.Game.IGame

/-!
# Adding or removing options
-/

noncomputable section

namespace IGame

/-- Inserts a new left option `y` for `x`. -/
def insertLeft (x y : IGame) : IGame :=
  {insert y x.leftMoves | x.rightMoves}ᴵ

/-- Inserts a new right option `y` for `x`. -/
def insertRight (x y : IGame) : IGame :=
  {x.leftMoves | insert y x.rightMoves}ᴵ

/-- Removes a left option `y` from `x`. -/
def removeLeft (x y : IGame) : IGame :=
  {x.leftMoves \ {y} | x.rightMoves}ᴵ

/-- Removes a right option `y` from `x`. -/
def removeRight (x y : IGame) : IGame :=
  {x.leftMoves | x.rightMoves \ {y}}ᴵ

end IGame
end
