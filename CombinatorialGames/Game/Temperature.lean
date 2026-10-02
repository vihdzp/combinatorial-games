/-
Copyright (c) 2026 Laurance Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurance Lau
-/
module

public import CombinatorialGames.Game.Small

import CombinatorialGames.Tactic.GameCmp

/-!
# Cooled games and temperature
-/

universe u

section

open IGame

notation "𝔻≥-1" => { t : Dyadic // -1 ≤ t }

instance : Zero 𝔻≥-1 := ⟨0, Dyadic.coe_le_zero.mp rfl⟩

open Classical in
noncomputable def cool (x : IGame) (t : 𝔻≥-1) : IGame :=
  let _cool τ := !{.range fun l : xᴸ ↦ cool l τ - τ | .range fun r : xᴿ ↦ cool r τ + τ}
  if hn : ∃ n : ℤ, x ≈ n then hn.choose else
    if hy : ∃ t', t' < t ∧ IsLeast {τ | ∃ y, Numeric y ∧ Infinitesimal (_cool τ - y)} t'
      then choose hy.choose_spec.right.left else _cool t
termination_by x
decreasing_by igame_wf

@[simp] theorem int_cool (x : ℤ) (t : 𝔻≥-1) : cool x t = x := by simp [cool]
@[simp] theorem nat_cool (x : ℕ) (t : 𝔻≥-1) : cool x t = x := int_cool x t
@[simp] theorem zero_cool (t : 𝔻≥-1) : cool 0 t = 0 := int_cool 0 t

/-- The IGame `x` cooled by `t` is equivalent to an integer or infinitesimally close to a number. -/
def frozen (x : IGame) (t : 𝔻≥-1) :=
  ∃ y, Numeric y ∧ Infinitesimal (!{(cool · t - t) '' xᴸ | (cool · t + t) '' xᴿ} - y)

theorem zero_frozen_neg_one : frozen 0 ⟨-1, neg_le_neg_iff.mpr rfl⟩ := by
  use 0
  simp [← zero_eq, Infinitesimal.zero]

theorem nat_frozen_neg_one (x : ℕ) : frozen x ⟨-1, neg_le_neg_iff.mpr rfl⟩ := by
  rcases x with _ | n
  · exact zero_frozen_neg_one
  · use n + 2
    refine ⟨inferInstance, (infinitesimal_iff _).mpr fun y hy ↦ ?_⟩
    constructor <;> norm_num <;> norm_cast <;> rw [← IGame.natCast_succ_eq]
    · rw [← Right.neg_neg_iff, ← Dyadic.toIGame_lt_zero] at hy
      exact hy.trans_antisymmRel (sub_self_equiv _).symm
    · exact (sub_self_equiv _).trans_lt <| Dyadic.zero_lt_toIGame.mpr hy

open Classical in
noncomputable def temperature (x : IGame) : 𝔻≥-1 := epsilon (IsLeast {τ | frozen x τ} ·)

end
