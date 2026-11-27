/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import CombinatorialGames.NatOrdinal.Basic
public import CombinatorialGames.Nimber.Basic

/-!
# Bound for nimber addition

This file proves that nimber addition is bounded above by natural addition.

This lets us conclude that `∗(ω ^ x)` is always a group, but we don't prove this here as it follows
more generally from every power of 2 being a group.
-/

public section

namespace Nimber

/-- A version of `add_le_nadd` stated in terms of `Ordinal`. -/
theorem add_le_nadd' (a b : Ordinal) : (∗a + ∗b).val ≤ (NatOrdinal.of a + NatOrdinal.of b).val := by
  rw [val_le_iff]
  apply add_le_of_forall_ne
  all_goals
    intro c hc
    cases c with | of c
    rw [← val_eq_iff.ne]
    apply ((add_le_nadd' ..).trans_lt _).ne
    simpa
termination_by (a, b)

theorem add_le_nadd (a b : Nimber) : a + b ≤ ∗(NatOrdinal.of a.val + NatOrdinal.of b.val).val :=
  add_le_nadd' ..

end Nimber
end
