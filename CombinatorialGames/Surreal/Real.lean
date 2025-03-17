/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.Surreal.Division
import Mathlib.Data.Real.Basic

/-!
# Real numbers as games

We define the function `Real.toIGame`
-/



namespace Rat

def toIGame (q : ℚ) : IGame :=
  q.num / (q.den : IGame)

end Rat
