/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Kim Morrison
-/
import CombinatorialGames.IGame.IGame
import Mathlib.Data.Countable.Small

/-!
# Short games

A combinatorial game is `Short` if it has only finitely many subpositions. In particular, this means
there is a finite set of moves at every point.

We historically defined `Short x` as data, which we then used to enable some degree of computation
on combinatorial games. This functionality is now implemented through the `game_cmp` tactic instead.
-/

universe u

namespace IGame

/-- A short game is one with finitely many subpositions.

Short games are those for which we can feasibly perform computations. To enable this, this typeclass
provides a term of an auxiliary type `SGame`, which mimics `PGame` but restricts the indexing types
to `Fin n`, alongside a proof that this term, casted in the obvious way to `IGame`, represents the
game in question. All computations can then go through `SGame`.

Unfortunately, well-founded recursion and reducibility don't mix very well in Lean. As such, we must
often rely on `native_decide` to make use of this typeclass for computation.

A prototypical instance looks something like this:

```
example : IGame.Short {{0, 2, 5} | {3, -1, 7}}ᴵ where
  toSGame := .ofLists [0, 2, 5] [3, -1, 7]
  toIGame_toSGame := by aesop
```
-/
class Short (x : IGame.{u}) : Type u where
  toSGame : SGame.{u}
  toIGame_toSGame : toSGame.toIGame = x

#exit
namespace Short
attribute [simp] toIGame_toSGame

@[simp]
theorem toSGame_le_iff {x y : IGame} [Short x] [Short y] : toSGame x ≤ toSGame y ↔ x ≤ y := by
  change (toSGame x).toIGame ≤ (toSGame y).toIGame ↔ x ≤ y
  simp

@[simp]
theorem toSGame_lt_iff {x y : IGame} [Short x] [Short y] : toSGame x < toSGame y ↔ x < y :=
  lt_iff_lt_of_le_iff_le' toSGame_le_iff toSGame_le_iff

instance (x y : IGame) [Short x] [Short y] : Decidable (x ≤ y) :=
  decidable_of_iff _ toSGame_le_iff

instance (x y : IGame) [Short x] [Short y] : Decidable (x < y) :=
  decidable_of_iff _ toSGame_lt_iff

instance (x y : IGame) [Short x] [Short y] : Decidable (x ≈ y) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance (x y : IGame) [Short x] [Short y] : Decidable (x = y) :=
  decidable_of_iff ((toSGame x).toIGame = (toSGame y).toIGame) (by simp)

instance : Short 0 := ⟨0, SGame.toIGame_zero⟩
instance : Short 1 := ⟨1, SGame.toIGame_one⟩

-- These should be computable: https://github.com/leanprover/lean4/pull/7283
noncomputable instance (n : ℕ) : Short n := ⟨n, SGame.toIGame_natCast n⟩
noncomputable instance (n : ℕ) [n.AtLeastTwo] : Short ofNat(n) := inferInstanceAs (Short n)

instance (x : IGame) [Short x] : Short (-x) := ⟨-toSGame x, by simp⟩
instance (x y : IGame) [Short x] [Short y] : Short (x + y) := ⟨toSGame x + toSGame y, by simp⟩
instance (x y : IGame) [Short x] [Short y] : Short (x - y) := ⟨toSGame x - toSGame y, by simp⟩
instance (x y : IGame) [Short x] [Short y] : Short (x * y) := ⟨toSGame x * toSGame y, by simp⟩

end Short

-- TODO: add some actual theorems

proof_wanted exists_lt_natCast_of_short (x : IGame) [Short x] : ∃ n : ℕ, x < n
proof_wanted exists_neg_natCast_lt_of_short (x : IGame) [Short x] : ∃ n : ℕ, -n < x

proof_wanted short_iff_finite_subposition (x : IGame) :
    Nonempty (Short x) ↔ Set.Finite {y | Subposition y x}

end IGame

section Test

example : (0 : IGame) < 1 := by decide
example : (-1 : IGame) < 0 := by native_decide
example : (0 : IGame) < 1 + 1 := by native_decide
example : (-1 : IGame) + 1 ≠ 0 := by native_decide
--example : (2 : IGame) < (5 : IGame) := by native_decide

end Test
