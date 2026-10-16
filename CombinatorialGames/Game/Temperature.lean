/-
Copyright (c) 2026 Laurance Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Laurance Lau
-/
module

public import CombinatorialGames.Game.Small

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.MinMax
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

inductive Trajectory : ℚ → Type
  | last (s a b : ℚ) : Trajectory s
  | cons (s t a b : ℚ) (h : s < t) (rest : Trajectory t) : Trajectory s

namespace Trajectory

def eval {s : ℚ} (τ : ℚ) : Trajectory s → ℚ
  | last _ a b => lineSegment τ a b
  | cons _ t a b _ rest => if τ ≤ t then lineSegment τ a b else rest.eval τ

private theorem _root_.exists_isLeast_eval_eq_zero' {a b t₁ t₂ : ℚ} (ha : a ≤ 0) (ht : t₁ < t₂)
    (h0 : 0 ∈ Set.Icc (lineSegment t₂ a b) (lineSegment t₁ a b)) :
    ∃ t ∈ Set.Icc t₁ t₂, IsLeast {t' ∈ Set.Icc t₁ t₂ | lineSegment t' a b = 0} t := by
  use if a = 0 then t₁ else -b / a
  grind [IsLeast, lowerBounds, le_div_iff_of_neg', div_le_iff_of_neg']

def Continuous {s : ℚ} : Trajectory s → Prop
  | last .. => True
  | cons _ t a b _ rest => lineSegment t a b = rest.eval t ∧ rest.Continuous

/-- Intermediate value theorem. -/
theorem exists_isLeast_eval_eq_zero {t t₁ t₂ : ℚ} (T : Trajectory t) (hC : T.Continuous)
    (ht : t₁ < t₂) (hT : AntitoneOn T.eval (Set.Icc t₁ t₂))
    (h0 : 0 ∈ Set.Icc (T.eval t₂) (T.eval t₁)) :
    ∃ τ ∈ Set.Icc t₁ t₂, IsLeast {t' ∈ Set.Icc t₁ t₂ | T.eval t' = 0} τ := by
  induction T generalizing t₁ t₂ with
  | last =>
      unfold eval at hT
      refine exists_isLeast_eval_eq_zero' ?_ ht h0
      nlinarith [hT ⟨le_rfl, ht.le⟩ ⟨ht.le, le_rfl⟩ ht.le]
  | cons s t a b hst rest ih =>
      let T := cons s t a b hst rest
      have hl {τ} (hτ : τ ≤ t) : T.eval τ = lineSegment τ a b := by simp [eval, hτ, T]
      by_cases h₂ : t₂ ≤ t
      · have : a ≤ 0 := by nlinarith [hl (ht.le.trans h₂), hl h₂, hT (by grind) (by grind) ht.le]
        obtain ⟨τ, h, _, _⟩ := exists_isLeast_eval_eq_zero' this ht
          (by rwa [← hl, ← hl (ht.le.trans h₂)])
        exact ⟨τ, h, by grind, by grind [lowerBounds]⟩
      · have hr {τ} (hτ : t ≤ τ) : T.eval τ = rest.eval τ := by grind [hC.left, eval]
        have hT' {l} (hl₁ : t₁ ≤ l) (hl₂ : t ≤ l) : AntitoneOn rest.eval (Set.Icc l t₂) := by
          intro _ ⟨ha₁, ha₂⟩ _ ⟨hb₁, hb₂⟩ hab
          grind [hC.left, eval, hT ⟨hl₁.trans ha₁, ha₂⟩ ⟨hl₁.trans hb₁, hb₂⟩ hab]
        by_cases h₁ : t₁ < t
        · by_cases he : T.eval t ≤ 0
          · have : a ≤ 0 := by nlinarith [hl le_rfl, hl h₁.le, hT (by grind) (by grind) h₁.le]
            obtain ⟨τ, _, _, _⟩ := exists_isLeast_eval_eq_zero' this h₁
              (by rw [← hl le_rfl, ← hl h₁.le]; exact ⟨he, h0.right⟩)
            exact ⟨τ, by grind, by grind, by grind [lowerBounds]⟩
          · obtain ⟨τ, _, _, _⟩ := ih hC.right (not_le.mp h₂) (hT' h₁.le le_rfl) (by grind)
            refine ⟨τ, by grind, by grind, fun τ' ⟨_, _⟩ ↦ ?_⟩
            by_cases hτ' : t ≤ τ'
            · grind [lowerBounds]
            · linarith [hT (by grind) (by grind) (not_le.mp hτ').le]
        · grind [ih hC.right ht (hT' le_rfl (not_lt.mp h₁)) (by grind)]

private def neg {s : ℚ} : Trajectory s → Trajectory s
  | last t a b => last t (-a) (-b)
  | cons s t a b h rest => cons s t (-a) (-b) h rest.neg

instance {s : ℚ} : Neg (Trajectory s) := ⟨neg⟩

@[simp] theorem eval_neg {s : ℚ} (T : Trajectory s) (τ : ℚ) :
    T.neg.eval τ = -T.eval τ := by
  induction T <;> grind [neg, eval]

theorem continuous_neg {s : ℚ} {T : Trajectory s} (h : T.Continuous) :
    T.neg.Continuous := by
  induction T with
  | last => trivial
  | cons s t a b hst rest ih => exact ⟨by grind [rest.eval_neg, h.left], ih h.right⟩

@[simp] def length {s : ℚ} : Trajectory s → ℕ
  | last .. => 1
  | cons _ _ _ _ _ rest => 1 + rest.length

@[simp] theorem length_congr {s t : ℚ} (h : s = t) (T : Trajectory s) :
    (h ▸ T : Trajectory t).length = T.length := by subst h; rfl

private def add {s : ℚ} : Trajectory s → Trajectory s → Trajectory s
  | last _ a₁ b₁, last _ a₂ b₂ => last s (a₁ + a₂) (b₁ + b₂)
  | last _ a₁ b₁, cons _ t₂ a₂ b₂ h₂ rest₂ =>
      cons s t₂ (a₁ + a₂) (b₁ + b₂) h₂ ((last t₂ a₁ b₁).add rest₂)
  | cons _ t₁ a₁ b₁ h₁ rest₁, last _ a₂ b₂ =>
      cons s t₁ (a₁ + a₂) (b₁ + b₂) h₁ (rest₁.add (last t₁ a₂ b₂))
  | cons _ t₁ a₁ b₁ h₁ rest₁, cons _ t₂ a₂ b₂ h₂ rest₂ =>
      if ht : t₁ = t₂ then
        cons s t₁ (a₁ + a₂) (b₁ + b₂) h₁ (rest₁.add (ht ▸ rest₂))
      else if ht : t₁ < t₂ then
        cons s t₁ (a₁ + a₂) (b₁ + b₂) h₁ (rest₁.add (cons t₁ t₂ a₂ b₂ ht rest₂))
      else
        have ht : t₁ > t₂ := by grind
        cons s t₂ (a₁ + a₂) (b₁ + b₂) h₂ ((cons t₂ t₁ a₁ b₁ ht rest₁).add rest₂)
termination_by T₁ T₂ => T₁.length + T₂.length
decreasing_by all_goals simp <;> omega

instance {s : ℚ} : Add (Trajectory s) := ⟨add⟩
instance {s : ℚ} : Sub (Trajectory s) := ⟨fun T₁ T₂ ↦ T₁ + (-T₂)⟩

@[grind]
private def maxAux (s t a₁ b₁ a₂ b₂ : ℚ) (hst : s < t) (k : Trajectory t) : Trajectory s :=
  if a₁ = a₂ then cons s t a₁ (max b₁ b₂) hst k else
    let τ₀ := (b₂ - b₁) / (a₁ - a₂)
    if hs : τ₀ ≤ s then
      if a₁ < a₂ then cons s t a₂ b₂ hst k else cons s t a₁ b₁ hst k
    else if ht : t ≤ τ₀ then
      if a₁ < a₂ then cons s t a₁ b₁ hst k else cons s t a₂ b₂ hst k
    else
      if a₁ < a₂ then cons s τ₀ a₁ b₁ (lt_of_not_ge hs) (cons τ₀ t a₂ b₂ (lt_of_not_ge ht) k)
        else cons s τ₀ a₂ b₂ (lt_of_not_ge hs) (cons τ₀ t a₁ b₁ (lt_of_not_ge ht) k)

private def max {s : ℚ} : Trajectory s → Trajectory s → Trajectory s
  | last _ a₁ b₁, last _ a₂ b₂ =>
      if a₁ = a₂ then last _ a₁ (Max.max b₁ b₂) else
        if hτ : (b₂ - b₁) / (a₁ - a₂) ≤ s then
          if a₁ < a₂ then last _ a₂ b₂ else last _ a₁ b₁
        else if a₁ < a₂ then cons _ _ a₁ b₁ (lt_of_not_ge hτ) (last _ a₂ b₂)
          else cons _ _ a₂ b₂ (lt_of_not_ge hτ) (last _ a₁ b₁)
  | last _ a₁ b₁, cons _ _ a₂ b₂ h₂ rest₂ =>
      maxAux _ _ a₁ b₁ a₂ b₂ h₂ (max (last _ a₁ b₁) rest₂)
  | cons _ _ a₁ b₁ h₁ rest₁, last _ a₂ b₂ =>
      maxAux _ _ a₁ b₁ a₂ b₂ h₁ (max rest₁ (last _ a₂ b₂))
  | cons _ t₁ a₁ b₁ h₁ rest₁, cons _ t₂ a₂ b₂ h₂ rest₂ =>
      if hlt : t₁ < t₂ then
        maxAux _ _ a₁ b₁ a₂ b₂ h₁ (max rest₁ (cons _ _ a₂ b₂ hlt rest₂))
      else if heq : t₁ = t₂ then
        maxAux _ _ a₁ b₁ a₂ b₂ h₁ (max rest₁ (heq ▸ rest₂))
      else
        maxAux _ _ a₁ b₁ a₂ b₂ h₂ (max (cons _ _ a₁ b₁ (by grind) rest₁) rest₂)
termination_by T₁ T₂ => T₁.length + T₂.length
decreasing_by all_goals simp <;> omega

instance {s : ℚ} : Max (Trajectory s) := ⟨max⟩

@[grind .] private lemma lineSegment_le_of_cross_le {a₁ b₁ a₂ b₂ τ : ℚ} (ha : a₁ < a₂)
    (hτ : (b₂ - b₁) / (a₁ - a₂) ≤ τ) : lineSegment τ a₁ b₁ ≤ lineSegment τ a₂ b₂ := by
  nlinarith [show a₁ * τ + b₁ - (a₂ * τ + b₂) = (a₁ - a₂) * (τ - (b₂ - b₁) / (a₁ - a₂)) by grind]

@[grind .] private lemma lineSegment_le_of_le_cross {a₁ b₁ a₂ b₂ τ : ℚ} (ha : a₁ < a₂)
    (hτ : τ ≤ (b₂ - b₁) / (a₁ - a₂)) : lineSegment τ a₂ b₂ ≤ lineSegment τ a₁ b₁ := by
  nlinarith [show a₁ * τ + b₁ - (a₂ * τ + b₂) = (a₁ - a₂) * (τ - (b₂ - b₁) / (a₁ - a₂)) by grind]

@[simp, grind =] theorem eval_last {s : ℚ} (a b : ℚ) (τ : ℚ) :
    (last s a b).eval τ = lineSegment τ a b := rfl

@[simp, grind =] theorem eval_cons_of_le {s : ℚ} (t a b : ℚ) (h : s < t)
    (rest : Trajectory t) {τ : ℚ} (hτ : τ ≤ t) :
    (cons s t a b h rest).eval τ = lineSegment τ a b := by
  simp [eval, hτ]

@[simp, grind =] theorem eval_cons_of_gt {s : ℚ} (t a b : ℚ) (h : s < t)
    (rest : Trajectory t) {τ : ℚ} (hτ : t < τ) :
    (cons s t a b h rest).eval τ = rest.eval τ := by
  simp [eval, hτ]

@[grind =] private theorem maxAux_eval_Icc {s t a₁ b₁ a₂ b₂ τ : ℚ} (hst : s < t) (k : Trajectory t)
    (hτ : τ ∈ Set.Icc s t) :
      (maxAux s t a₁ b₁ a₂ b₂ hst k).eval τ =
        Max.max (lineSegment τ a₁ b₁) (lineSegment τ a₂ b₂) := by
  obtain ⟨hsτ, hτt⟩ := hτ
  by_cases ha : a₁ = a₂
  · simp [maxAux, ha, eval_cons_of_le (hτ := hτt), add_max]
  · grind [le_antisymm]

@[grind =] private theorem maxAux_eval_Ioi {s t a₁ b₁ a₂ b₂ τ : ℚ} (hst : s < t) (k : Trajectory t)
    (hτ : τ ∈ Set.Ioi t) : (maxAux s t a₁ b₁ a₂ b₂ hst k).eval τ = k.eval τ := by grind

@[simp]
theorem eval_max {s τ : ℚ} (T₁ T₂ : Trajectory s) (hC₁ : T₁.Continuous) (hC₂ : T₂.Continuous)
    (hsτ : τ ≥ s) : (max T₁ T₂).eval τ = Max.max (T₁.eval τ) (T₂.eval τ) := by
  match T₁, T₂ with
  | last _ a₁ _, last _ a₂ _ => grind [max, le_antisymm]
  | last _ a₁ b₁, cons _ t₂ .. =>
      by_cases hτt₂ : τ ≤ t₂
      · grind [max]
      · grind [max, eval_max (last t₂ a₁ b₁) _ hC₁ hC₂.right (le_of_not_ge hτt₂)]
  | cons _ t₁ .., last _ a₂ b₂ =>
      by_cases hτt₁ : τ ≤ t₁
      · grind [max]
      · grind [max, eval_max _ (last t₁ a₂ b₂) hC₁.right hC₂ (le_of_not_ge hτt₁)]
  | cons _ t₁ a₁ b₁ _ rest₁, cons _ t₂ a₂ b₂ _ rest₂ =>
      unfold max
      rcases lt_trichotomy t₁ t₂ with ht | ht | ht
      · by_cases hτt₁ : τ ≤ t₁
        · grind
        · grind [eval_max _ (cons t₁ t₂ a₂ b₂ ht rest₂) hC₁.right hC₂ (le_of_not_ge hτt₁)]
      · by_cases hτt₁ : τ ≤ t₁
        · grind
        · grind [eval_max _ (ht ▸ rest₂) hC₁.right (ht ▸ hC₂.right) (le_of_not_ge hτt₁)]
      · by_cases hτt₂ : τ ≤ t₂
        · grind
        · grind [eval_max (cons t₂ t₁ a₁ b₁ ht rest₁) _ hC₁ hC₂.right (le_of_not_ge hτt₂)]
termination_by T₁.length + T₂.length
decreasing_by all_goals simp <;> omega

private theorem maxAux_continuous {s t a₁ b₁ a₂ b₂ : ℚ} (hst : s < t) {T : Trajectory t}
    (hk : T.Continuous) (hmax : Max.max (lineSegment t a₁ b₁) (lineSegment t a₂ b₂) = T.eval t) :
    (maxAux s t a₁ b₁ a₂ b₂ hst T).Continuous := by
  have : (maxAux s t a₁ b₁ a₂ b₂ hst T).eval t = T.eval t := by grind
  unfold maxAux
  by_cases ha : a₁ = a₂
  · simpa only [ha] using ⟨by grind, hk⟩
  · by_cases hs : (b₂ - b₁) / (a₁ - a₂) ≤ s
    · by_cases hlt : a₁ < a₂ <;> simpa only [ha, hs, hlt] using ⟨by grind, hk⟩
    · by_cases ht : t ≤ (b₂ - b₁) / (a₁ - a₂)
      · by_cases hlt : a₁ < a₂ <;> simpa only [ha, hs, ht, hlt] using ⟨by grind, hk⟩
      · by_cases hlt : a₁ < a₂ <;> simpa only [ha, hs, ht, hlt] using ⟨by grind, by grind, hk⟩

theorem max_continuous {s : ℚ} {T₁ T₂ : Trajectory s} (hC₁ : T₁.Continuous) (hC₂ : T₂.Continuous) :
    (max T₁ T₂).Continuous := by
  match T₁, T₂ with
  | last _ a₁ b₁, last _ a₂ b₂ => grind [max, Continuous]
  | last _ a₁ b₁, cons _ t₂ a₂ b₂ h₂ rest₂ =>
      unfold max
      apply maxAux_continuous h₂ (max_continuous (by trivial) hC₂.right)
      simp [eval_max (last t₂ a₁ b₁) _ (by trivial) hC₂.right, hC₂.left]
  | cons _ t₁ a₁ b₁ h₁ rest₁, last _ a₂ b₂ =>
      unfold max
      apply maxAux_continuous h₁ (max_continuous hC₁.right (by trivial))
      simp [eval_max _ (last t₁ a₂ b₂) hC₁.right (by trivial), hC₁.left]
  | cons _ t₁ a₁ b₁ h₁ rest₁, cons _ t₂ a₂ b₂ h₂ rest₂ =>
      rcases lt_trichotomy t₁ t₂ with ht | heq | ht
      · simp only [max, ht]
        apply maxAux_continuous h₁ (max_continuous hC₁.right hC₂)
        grind [eval_max _ (cons _ _ a₂ b₂ ht rest₂) hC₁.right hC₂ le_rfl, hC₁.left]
      · simp only [max, heq, lt_self_iff_false]
        apply maxAux_continuous h₁ (max_continuous hC₁.right (heq ▸ hC₂.right))
        subst heq
        rw [eval_max _ _ hC₁.right hC₂.right le_rfl, hC₁.left, hC₂.left]
      · simp only [max, not_lt_of_gt ht, ne_of_gt ht]
        apply maxAux_continuous h₂ (max_continuous hC₁ hC₂.right)
        grind [eval_max (cons _ _ a₁ b₁ ht rest₁) _ hC₁ hC₂.right le_rfl, hC₂.left]
termination_by T₁.length + T₂.length
decreasing_by all_goals simp <;> omega

def min {s : ℚ} (T₁ T₂ : Trajectory s) : Trajectory s := (max (T₁.neg) (T₂.neg)).neg

instance {s : ℚ} : Min (Trajectory s) := ⟨min⟩

@[simp]
theorem eval_min {s τ : ℚ} (T₁ T₂ : Trajectory s) (hC₁ : T₁.Continuous) (hC₂ : T₂.Continuous)
    (hsτ : τ ≥ s) : (min T₁ T₂).eval τ = Min.min (T₁.eval τ) (T₂.eval τ) := by
  simp [min, eval_max _ _ (continuous_neg hC₁) (continuous_neg hC₂) hsτ, max_neg_neg]

theorem min_continuous {s : ℚ} {T₁ T₂ : Trajectory s} (hC₁ : T₁.Continuous) (hC₂ : T₂.Continuous) :
    (T₁.min T₂).Continuous :=
  continuous_neg (max_continuous (continuous_neg hC₁) (continuous_neg hC₂))

def shiftPos {s : ℚ} : Trajectory s → Trajectory s
  | last t a b => last t (a + 1) b
  | cons s t a b h rest => cons s t (a + 1) b h rest.shiftPos

@[simp, grind =] theorem eval_shiftPos {s : ℚ} (T : Trajectory s) (τ : ℚ) :
    T.shiftPos.eval τ = T.eval τ + τ := by
  induction T <;> grind [shiftPos, eval]

theorem continuous_shiftPos {s : ℚ} {T : Trajectory s} (h : T.Continuous) :
    T.shiftPos.Continuous := by
  induction T with
  | last => trivial
  | cons s t a b h' rest ih => exact ⟨by grind [h.left, h.right], ih h.right⟩

def shiftNeg {s : ℚ} : Trajectory s → Trajectory s
  | last t a b => last t (a - 1) b
  | cons s t a b h rest => cons s t (a - 1) b h rest.shiftNeg

@[simp, grind =] theorem eval_shiftNeg {s : ℚ} (T : Trajectory s) (τ : ℚ) :
    T.shiftNeg.eval τ = T.eval τ - τ := by
  induction T <;> grind [shiftNeg, eval]

theorem continuous_shiftNeg {s : ℚ} {T : Trajectory s} (h : T.Continuous) :
    T.shiftNeg.Continuous := by
  induction T with
  | last => trivial
  | cons s t a b h' rest ih => exact ⟨by grind [h.left, h.right], ih h.right⟩

def truncate {s : ℚ} : Trajectory s → ℚ → Trajectory s
  | last _ a b, t' =>
      if h : s < t' then cons _ _ a b h (last _ 0 (lineSegment t' a b))
      else last s 0 (lineSegment t' a b)
  | cons _ t a b h rest, t' =>
      if h' : s < t' then
        if t' ≤ t then cons _ _ a b h' (last t' 0 (lineSegment t' a b))
        else cons s t a b h (rest.truncate t')
      else last s 0 (lineSegment t' a b)

@[simp, grind =] theorem eval_truncate {s : ℚ} (T : Trajectory s) (t' τ : ℚ) (hsτ : s ≤ τ) :
    (T.truncate t').eval τ = if τ ≤ t' then T.eval τ else T.eval t' := by
  induction T <;> grind [truncate]

theorem continuous_truncate {s : ℚ} (T : Trajectory s) (hC : T.Continuous) (t' : ℚ) :
    (T.truncate t').Continuous := by
  induction T with
  | last s a b =>
      unfold truncate
      split
      · exact ⟨by simp, trivial⟩
      · trivial
  | cons s t a b h₀ rest ih =>
      unfold truncate
      split_ifs
      · exact ⟨by simp, trivial⟩
      · exact ⟨by grind [hC.left], by grind [hC.right]⟩
      · trivial

end Trajectory

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
/-- The game `x` cooled by `t`. -/
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

/-- The game `x` cooled by `t` is equivalent to an integer or infinitesimally close to a number. -/
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
