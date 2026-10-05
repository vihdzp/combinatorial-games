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
instance : One 𝔻≥-1 := ⟨1, Dyadic.coe_le_one.mp rfl⟩

open Classical in
/-- The IGame `x` cooled by `t`. -/
noncomputable def cool (x : IGame) (t : 𝔻≥-1) : IGame :=
  let _cool τ := !{.range fun l : xᴸ ↦ cool l τ - τ | .range fun r : xᴿ ↦ cool r τ + τ}
  if hn : ∃ n : ℤ, x ≈ n then hn.choose else
    if hy : ∃ t', t' < t ∧ IsLeast {τ | ∃ y, Numeric y ∧ Small (_cool τ - y)} t'
      then choose hy.choose_spec.right.left else _cool t
termination_by x
decreasing_by igame_wf

@[simp] theorem cool_intCast (x : ℤ) (t : 𝔻≥-1) : cool x t = x := by simp [cool]
@[simp] theorem cool_natCast (x : ℕ) (t : 𝔻≥-1) : cool x t = x := cool_intCast x t
@[simp] theorem cool_zero (t : 𝔻≥-1) : cool 0 t = 0 := cool_intCast 0 t
@[simp] theorem cool_one (t : 𝔻≥-1) : cool 1 t = 1 := by simpa using cool_intCast 1 t

/-- The IGame `x` cooled by `t` is equivalent to an integer or infinitesimally close to a number. -/
def Frozen (x : IGame) (t : 𝔻≥-1) : Prop :=
  ∃ y, Numeric y ∧ Small (!{(cool · t - t) '' xᴸ | (cool · t + t) '' xᴿ} - y)

theorem frozen_of_numeric {x : IGame} {t : 𝔻≥-1}
    (H : Numeric !{(cool · t - t) '' xᴸ | (cool · t + t) '' xᴿ}) : Frozen x t :=
  ⟨_, H, .of_equiv (sub_self_equiv _).symm⟩

theorem frozen_intCast (n : ℤ) (t : 𝔻≥-1) : Frozen n t := by
  apply frozen_of_numeric
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg <;> constructor
  · simp
  · suffices ∀ a ∈ nᴸ, (cool a t - t).Numeric by simpa
    intro m hm
    obtain ⟨m, hmn, rfl⟩ := eq_natCast_of_mem_leftMoves_natCast hm
    rw [cool_natCast]
    exact Numeric.sub ..
  · simp
  · suffices ∀ a ∈ nᴸ, (cool (-a) t + t).Numeric by simpa
    intro m hm
    obtain ⟨m, hmn, rfl⟩ := eq_natCast_of_mem_leftMoves_natCast hm
    rw [← intCast_nat, ← intCast_neg, cool_intCast]
    exact Numeric.add ..

theorem frozen_natCast (n : ℕ) (t : 𝔻≥-1) : Frozen n t := frozen_intCast n t
theorem frozen_zero (t : 𝔻≥-1) : Frozen 0 t := frozen_intCast 0 t

open Classical in
/-- The IGame `x` is first frozen at temperature `t`. -/
noncomputable def temperature (x : IGame) : 𝔻≥-1 := epsilon (IsLeast {τ | Frozen x τ} ·)

open Classical in
theorem temperature_of_frozen_neg_one {x : IGame} (h : Frozen x ⟨-1, neg_le_neg_iff.mpr rfl⟩) :
    temperature x = ⟨-1, neg_le_neg_iff.mpr rfl⟩ :=
  IsLeast.unique (epsilon_spec ⟨_, h, fun _ ↦ by aesop⟩) ⟨h, fun _ ↦ by aesop⟩

@[simp]
theorem temperature_zero_eq_neg_one : temperature 0 = ⟨-1, neg_le_neg_iff.mpr rfl⟩ :=
  temperature_of_frozen_neg_one (frozen_zero _)

@[simp]
theorem temperature_nat_eq_neg_one (x : ℕ) : temperature x = ⟨-1, neg_le_neg_iff.mpr rfl⟩ :=
  temperature_of_frozen_neg_one (frozen_natCast ..)

end
