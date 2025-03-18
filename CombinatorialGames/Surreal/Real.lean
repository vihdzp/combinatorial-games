/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.Surreal.Division
import Mathlib.Data.Real.Basic

/-!
# Real numbers as games

We define the function `Real.toIGame`, casting a real number to its Dedekind cut, and prove that
it's an order embedding. We then define the `Game` and `Surreal` versions of this map, and prove
that they are ring and field homomorphisms respectively.

## TODO

Every real number has birthday at most `ω`. This can be proven by showing that a real number is
equivalent to its Dedekind cut where only dyadic rationals are considered. At a later point, after
we have the necessary API on dyadic numbers, we might want to prove this equivalence, or even
re-define real numbers as Dedekind cuts of dyadic numbers specifically.
-/

namespace Real

def toIGame : ℝ ↪o IGame := by
  refine .ofStrictMono (fun x ↦ {(↑) '' {q : ℚ | q < x} | (↑) '' {q : ℚ | x < q}}ᴵ)
    fun x y h ↦ lt_of_le_not_le ?_ ?_
  · 

end Real
