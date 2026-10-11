/-
Copyright (c) 2026 Laurance Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurance Lau
-/
module

public import CombinatorialGames.Game.Small

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Basic

/-!
# Cooled games and temperature
-/

universe u

section

open IGame

notation "𝔻≥-1" => { t : Dyadic // -1 ≤ t }

instance : Zero 𝔻≥-1 := ⟨0, by decide⟩
instance : One 𝔻≥-1 := ⟨1, by decide⟩

abbrev lineSegment (t a b : ℚ) : ℚ := a * t + b

inductive Trajectory : ℚ → ℚ → Type
  | last (s a b : ℚ) : Trajectory s (lineSegment s a b)
  | cons (s t a b v : ℚ) (h : s < t) (rest : Trajectory t v) (hv : lineSegment t a b = v) :
      Trajectory s (lineSegment s a b)

def Trajectory.eval {s v : ℚ} (τ : ℚ) : Trajectory s v → ℚ
  | .last _ a b => lineSegment τ a b
  | .cons _ t a b _ _ rest _ => if τ ≤ t then lineSegment τ a b else rest.eval τ

@[simp] private theorem Trajectory.eval_start {s v : ℚ} (T : Trajectory s v) : T.eval s = v := by
  unfold Trajectory.eval
  split <;> grind

private theorem exists_isLeast_eval_eq_zero' {a b t₁ t₂ : ℚ} (ha : a ≤ 0) (ht : t₁ < t₂)
    (h0 : 0 ∈ Set.Icc (lineSegment t₂ a b) (lineSegment t₁ a b)) :
    ∃ t ∈ Set.Icc t₁ t₂, IsLeast {t' ∈ Set.Icc t₁ t₂ | lineSegment t' a b = 0} t := by
  have (h : a < 0) := (le_div_iff_of_neg' h).mpr (Rat.le_add_iff_sub_le.mp h0.right)
  have (h : a < 0) := (div_le_iff_of_neg' h).mpr (Rat.add_le_iff_le_sub.mp h0.left)
  use if a = 0 then t₁ else -b / a
  grind [IsLeast, lowerBounds]

/-- Intermediate value theorem. -/
theorem exists_isLeast_eval_eq_zero {t v t₁ t₂ : ℚ} (T : Trajectory t v) (ht : t₁ < t₂)
    (hT : AntitoneOn T.eval (Set.Icc t₁ t₂)) (h0 : 0 ∈ Set.Icc (T.eval t₂) (T.eval t₁)) :
    ∃ τ ∈ Set.Icc t₁ t₂, IsLeast {t' ∈ Set.Icc t₁ t₂ | T.eval t' = 0} τ := by
  induction T generalizing t₁ t₂ with
  | last =>
      unfold Trajectory.eval at hT
      refine exists_isLeast_eval_eq_zero' ?_ ht h0
      nlinarith [hT ⟨le_rfl, ht.le⟩ ⟨ht.le, le_rfl⟩ ht.le]
  | cons _ t a b _ h rest hv ih =>
    let T := Trajectory.cons _ t a b _ h rest hv
    have hl {τ} (hτ : τ ≤ t) : T.eval τ = lineSegment τ a b := by simp [Trajectory.eval, hτ, T]
    by_cases h₂ : t₂ ≤ t
    · have : a ≤ 0 := by nlinarith [hl (ht.le.trans h₂), hl h₂, hT (by grind) (by grind) ht.le]
      obtain ⟨τ, h, _, _⟩ := exists_isLeast_eval_eq_zero' this ht
        (by rwa [← hl, ← hl (ht.le.trans h₂)])
      exact ⟨τ, h, by grind, by grind [lowerBounds]⟩
    · have hr {τ} (hτ : t ≤ τ) : T.eval τ = rest.eval τ := by
        by_cases hτt : τ ≤ t
        · simp [T, Trajectory.eval, hv, le_antisymm hτt hτ]
        · simp [T, Trajectory.eval, hτt]
      have hT' {l} (hl₁ : t₁ ≤ l) (hl₂ : t ≤ l) : AntitoneOn rest.eval (Set.Icc l t₂) := by
        intro _ ⟨ha₁, ha₂⟩ _ ⟨hb₁, hb₂⟩ hab
        grind [hT ⟨hl₁.trans ha₁, ha₂⟩ ⟨hl₁.trans hb₁, hb₂⟩ hab]
      by_cases h₁ : t₁ < t
      · by_cases he : T.eval t ≤ 0
        · have : a ≤ 0 := by nlinarith [hl le_rfl, hl h₁.le, hT (by grind) (by grind) h₁.le]
          obtain ⟨τ, _, _, _⟩ := exists_isLeast_eval_eq_zero' this h₁
            (by rw [← hl le_rfl, ← hl h₁.le]; exact ⟨he, h0.right⟩)
          exact ⟨τ, by grind, by grind, by grind [lowerBounds]⟩
        · obtain ⟨τ, _, _, _⟩ := ih (not_le.mp h₂) (hT' h₁.le le_rfl) (by grind)
          refine ⟨τ, by grind, by grind, fun τ' ⟨_, _⟩ ↦ ?_⟩
          by_cases hτ' : t ≤ τ'
          · grind [lowerBounds]
          · linarith [hT (by grind) (by grind) (not_le.mp hτ').le]
      · have hr {τ} (hτ : t₁ ≤ τ) := hr ((not_lt.mp h₁).trans hτ)
        obtain ⟨τ, h, _, _⟩ := ih ht (hT' le_rfl (not_lt.mp h₁)) (by rwa [← hr ht.le, ← hr le_rfl])
        exact ⟨τ, h, by grind, by grind⟩

open Classical in
mutual

noncomputable def leftWall (x : IGame) (t : 𝔻≥-1) : ℚ :=
  if hn : ∃ n : ℤ, x ≈ n then hn.choose else
    if ht' : ∃ t' < t, IsLeast {τ | leftScaffold x τ = rightScaffold x τ} t'
      then leftScaffold x ht'.choose else leftScaffold x t
termination_by (x, 1)
decreasing_by igame_wf

noncomputable def rightWall (x : IGame) (t : 𝔻≥-1) : ℚ :=
  if hn : ∃ n : ℤ, x ≈ n then hn.choose else
    if ht' : ∃ t' < t, IsLeast {τ | leftScaffold x τ = rightScaffold x τ} t'
      then rightScaffold x ht'.choose else rightScaffold x t
termination_by (x, 1)
decreasing_by igame_wf

noncomputable def leftScaffold (x : IGame) (t : 𝔻≥-1) : ℚ :=
  epsilon (IsGreatest (.range fun l : xᴸ ↦ rightWall l t - (t : ℚ)))
termination_by (x, 0)
decreasing_by igame_wf

noncomputable def rightScaffold (x : IGame) (t : 𝔻≥-1) : ℚ :=
  epsilon (IsLeast (.range fun r : xᴿ ↦ leftWall r t + (t : ℚ)))
termination_by (x, 0)
decreasing_by igame_wf

end

open Classical in
/-- The IGame `x` cooled by `t`. -/
noncomputable def cool (x : IGame) (t : 𝔻≥-1) : IGame :=
  let _cool τ := !{.range fun l : xᴸ ↦ cool l τ - τ | .range fun r : xᴿ ↦ cool r τ + τ}
  if hn : ∃ n : ℤ, x ≈ n then hn.choose else
    if hy : ∃ t', t' < t ∧ IsLeast {τ | ∃ y, Numeric y ∧ Infinitesimal (_cool τ - y)} t'
      then choose hy.choose_spec.right.left else _cool t
termination_by x
decreasing_by igame_wf

@[simp] theorem cool_intCast (x : ℤ) (t : 𝔻≥-1) : cool x t = x := by simp [cool]
@[simp] theorem cool_natCast (x : ℕ) (t : 𝔻≥-1) : cool x t = x := cool_intCast x t
@[simp] theorem cool_zero (t : 𝔻≥-1) : cool 0 t = 0 := cool_intCast 0 t
@[simp] theorem cool_one (t : 𝔻≥-1) : cool 1 t = 1 := by simpa using cool_intCast 1 t

/-- The IGame `x` cooled by `t` is equivalent to an integer or infinitesimally close to a number. -/
def Frozen (x : IGame) (t : 𝔻≥-1) : Prop :=
  ∃ y, Numeric y ∧ Infinitesimal (!{(cool · t - t) '' xᴸ | (cool · t + t) '' xᴿ} - y)

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
theorem temperature_zero : temperature 0 = ⟨-1, neg_le_neg_iff.mpr rfl⟩ :=
  temperature_of_frozen_neg_one (frozen_zero _)

@[simp]
theorem temperature_natCast (x : ℕ) : temperature x = ⟨-1, neg_le_neg_iff.mpr rfl⟩ :=
  temperature_of_frozen_neg_one (frozen_natCast ..)

@[simp]
theorem temperature_intCast (x : ℤ) : temperature x = ⟨-1, neg_le_neg_iff.mpr rfl⟩ :=
  temperature_of_frozen_neg_one (frozen_intCast ..)

end
