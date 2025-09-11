/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.NatOrdinal.Basic
import Mathlib.SetTheory.Ordinal.Exponential

/-!
# Natural operations on `ω ^ x`

In the future, this file will show various results relating to natural ordinal arithmetic on
additive principal ordinals. At the moment however, this file is just a stub defining the `Wpow`
notation typeclass, and transferring the most basic results on `ω ^ x` from `Ordinal` to
`NatOrdinal`.
-/

open Ordinal

/-- A typeclass for the the `ω^` notation. -/
class Wpow (α : Type*) where
  wpow : α → α

prefix:75 "ω^ " => Wpow.wpow
recommended_spelling "wpow" for "ω^" in [«termω^_»]

namespace NatOrdinal

noncomputable instance : Wpow NatOrdinal where
  wpow x := of (ω ^ x.val)

theorem wpow_def (x : NatOrdinal) : ω^ x = of (ω ^ x.val) := rfl

theorem wpow_strictMono : StrictMono (ω^ · : NatOrdinal → NatOrdinal) :=
  Ordinal.opow_lt_opow_iff_right

#exit
theorem omega0_opow_mul_nat_lt {a b : Ordinal} (h : a < b) (n : ℕ) : ω ^ a * n < ω ^ b := by
  apply lt_of_lt_of_le _ (opow_le_opow_right omega0_pos (succ_le_of_lt h))
  rw [opow_succ]
  exact mul_lt_mul_of_pos_left (nat_lt_omega0 n) (opow_pos a omega0_pos)

theorem lt_omega0_opow {a b : Ordinal} (hb : b ≠ 0) :
    a < ω ^ b ↔ ∃ c < b, ∃ n : ℕ, a < ω ^ c * n := by
  refine ⟨fun ha ↦ ⟨_, lt_log_of_lt_opow hb ha, ?_⟩,
    fun ⟨c, hc, n, hn⟩ ↦ hn.trans (omega0_opow_mul_nat_lt hc n)⟩
  obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt a one_lt_omega0)
  use n.succ
  rw [natCast_succ, ← hn]
  exact lt_mul_succ_div a (opow_ne_zero _ omega0_ne_zero)

theorem lt_omega0_opow_succ {a b : Ordinal} : a < ω ^ succ b ↔ ∃ n : ℕ, a < ω ^ b * n := by
  refine ⟨fun ha ↦ ?_, fun ⟨n, hn⟩ ↦ hn.trans (omega0_opow_mul_nat_lt (lt_succ b) n)⟩
  obtain ⟨c, hc, n, hn⟩ := (lt_omega0_opow (succ_ne_zero b)).1 ha
  refine ⟨n, hn.trans_le (mul_le_mul_right' ?_ _)⟩
  rwa [opow_le_opow_iff_right one_lt_omega0, ← lt_succ_iff]

end NatOrdinal
