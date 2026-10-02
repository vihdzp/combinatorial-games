/-
Copyright (c) 2026 Laurance Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurance Lau
-/
module

public import CombinatorialGames.Game.Small

import Mathlib.Tactic.NormNum.Basic

/-!
# Cooled games and temperature
-/

universe u

section

open IGame

notation "𝔻≥-1" => { t : Dyadic // -1 ≤ t }

instance : Zero 𝔻≥-1 := ⟨0, Dyadic.coe_le_zero.mp rfl⟩

open Classical in
/-- The IGame `x` cooled by `t`. -/
noncomputable def cool (x : IGame) (t : 𝔻≥-1) : IGame :=
  let _cool τ := !{.range fun l : xᴸ ↦ cool l τ - τ | .range fun r : xᴿ ↦ cool r τ + τ}
  if hn : ∃ n : ℤ, x ≈ n then hn.choose else
    if hy : ∃ t', t' < t ∧ IsLeast {τ | ∃ y, Numeric y ∧ Small (_cool τ - y)} t'
      then choose hy.choose_spec.right.left else _cool t
termination_by x
decreasing_by igame_wf

@[simp] theorem int_cool (x : ℤ) (t : 𝔻≥-1) : cool x t = x := by simp [cool]
@[simp] theorem nat_cool (x : ℕ) (t : 𝔻≥-1) : cool x t = x := int_cool x t
@[simp] theorem zero_cool (t : 𝔻≥-1) : cool 0 t = 0 := int_cool 0 t

/-- The IGame `x` cooled by `t` is equivalent to an integer or infinitesimally close to a number. -/
def frozen (x : IGame) (t : 𝔻≥-1) :=
  ∃ y, Numeric y ∧ Small (!{(cool · t - t) '' xᴸ | (cool · t + t) '' xᴿ} - y)

theorem zero_frozen_neg_one : frozen 0 ⟨-1, neg_le_neg_iff.mpr rfl⟩ := by
  use 0
  simp [← zero_eq, Small.zero]

theorem nat_frozen_neg_one (x : ℕ) : frozen x ⟨-1, neg_le_neg_iff.mpr rfl⟩ := by
  rcases x with _ | n
  · exact zero_frozen_neg_one
  · use n + 2
    refine ⟨inferInstance, fun hy ↦ ?_, fun hy ↦ ?_⟩
    all_goals norm_num; norm_cast; rw [← IGame.natCast_succ_eq]
    · exact (sub_self_equiv _).trans_lt hy
    · exact hy.trans_antisymmRel (sub_self_equiv _).symm

proof_wanted int_frozen_neg_one (x : ℤ) : frozen x ⟨-1, neg_le_neg_iff.mpr rfl⟩

open Classical in
/-- The IGame `x` is first frozen at temperature `t`. -/
noncomputable def temperature (x : IGame) : 𝔻≥-1 := epsilon (IsLeast {τ | frozen x τ} ·)

open Classical in
theorem temperature_of_frozen_neg_one {x : IGame} (h : frozen x ⟨-1, neg_le_neg_iff.mpr rfl⟩) :
    temperature x = ⟨-1, neg_le_neg_iff.mpr rfl⟩ :=
  IsLeast.unique (epsilon_spec ⟨_, h, fun _ ↦ by aesop⟩) ⟨h, fun _ ↦ by aesop⟩

end
