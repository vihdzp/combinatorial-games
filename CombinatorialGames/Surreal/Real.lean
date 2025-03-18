/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.Surreal.Division
import Mathlib.Data.Real.Archimedean

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

open IGame

noncomputable section

@[simp, norm_cast]
theorem IGame.ratCast_pos {q : ℚ} : 0 < (q : IGame) ↔ 0 < q := by
  simpa using ratCast_lt (m := 0)

theorem IGame.ratCast_add_equiv (q r : ℚ) : ((q + r : ℚ) : IGame) ≈ q + r := by
  simp [← Surreal.mk_eq_mk]

theorem IGame.ratCast_sub_equiv (q r : ℚ) : ((q - r : ℚ) : IGame) ≈ q - r := by
  simp [← Surreal.mk_eq_mk]

theorem IGame.ratCast_mul_equiv (q r : ℚ) : ((q * r : ℚ) : IGame) ≈ q * r := by
  simp [← Surreal.mk_eq_mk]

theorem IGame.ratCast_inv_equiv {q : ℚ} (hq : 0 < q) : ((q⁻¹ : ℚ) : IGame) ≈ q⁻¹ := by
  have := Numeric.inv (x := q) (by simpa)
  rw [← Surreal.mk_eq_mk, Surreal.mk_inv_of_pos (by simpa)]
  simp

theorem IGame.ratCast_div_equiv (q : ℚ) {r : ℚ} (hr : 0 < r) : ((q / r : ℚ) : IGame) ≈ q / r := by
  have := Numeric.inv (x := r) (by simpa)
  rw [← Surreal.mk_eq_mk, Surreal.mk_div_of_pos _ (by simpa)]
  simp

theorem IGame.Numeric.lt_div_iff {x y z : IGame} [Numeric x] [Numeric y] [Numeric z]
    (hz : 0 < z) : x < y / z ↔ x * z < y := by
  have := Numeric.inv hz
  rw [← Surreal.mk_lt_mk, Surreal.mk_div_of_pos y hz]
  exact lt_div_iff₀ hz

theorem IGame.Numeric.div_lt_iff {x y z : IGame} [Numeric x] [Numeric y] [Numeric z]
    (hy : 0 < y) : x / y < z ↔ x < z * y := by
  have := Numeric.inv hy
  rw [← Surreal.mk_lt_mk, Surreal.mk_div_of_pos x hy]
  exact div_lt_iff₀ hy

theorem IGame.Numeric.lt_div_iff_of_neg {x y : IGame} {q : ℚ} [Numeric x] [Numeric y]
    (hq : q < 0) : x < y * q⁻¹ ↔ y < x * q := by
  rw [← Surreal.mk_lt_mk, Surreal.mk_mul, ← _root_.lt_div_iff_of_neg]
  · rw [Surreal.mk_ratCast, Rat.cast_inv, div_inv_eq_mul, ← Surreal.mk_ratCast]
    rfl
  · simpa

    #exit

-- TODO: upstream
open Pointwise in
theorem Set.neg_image {α β : Type*} [InvolutiveNeg α] [InvolutiveNeg β]
    {s : Set β} {f : β → α} (h : ∀ x ∈ s, f (-x) = -f x) : -f '' s = f '' (-s) := by
  simp_rw [← Set.image_neg_eq_neg, Set.image_image]
  aesop

namespace Real

/-! ### `ℝ` to `IGame` -/

/-- We make this private until we can build the `OrderEmbedding`. -/
private def toIGame' (x : ℝ) : IGame :=
  {(↑) '' {q : ℚ | q < x} | (↑) '' {q : ℚ | x < q}}ᴵ

private theorem Numeric.toIGame' (x : ℝ) : Numeric (toIGame' x) := by
  rw [Real.toIGame']
  apply Numeric.mk' <;> simp only [leftMoves_ofSets, rightMoves_ofSets, Set.forall_mem_image]
  · intro x hx y hy
    dsimp at *
    exact_mod_cast hx.trans hy
  all_goals
    intros
    infer_instance

/-- The canonical map from `ℝ` to `IGame`, sending a real number to its Dedekind cut. -/
def toIGame : ℝ ↪o IGame := by
  refine .ofStrictMono toIGame' fun x y h ↦ ?_
  have := Numeric.toIGame' x
  have := Numeric.toIGame' y
  obtain ⟨q, hx, hy⟩ := exists_rat_btwn h
  trans (q : IGame)
  · apply Numeric.lt_rightMove
    simpa [toIGame']
  · apply Numeric.leftMove_lt
    simpa [toIGame']

theorem toIGame_def (x : ℝ) : x.toIGame = {(↑) '' {q : ℚ | q < x} | (↑) '' {q : ℚ | x < q}}ᴵ :=
  rfl

instance (x : ℝ) : Numeric x.toIGame :=
  Numeric.toIGame' x

@[simp]
theorem leftMoves_toIGame (x : ℝ) : x.toIGame.leftMoves = (↑) '' {q : ℚ | q < x} :=
  leftMoves_ofSets ..

@[simp]
theorem rightMoves_toIGame (x : ℝ) : x.toIGame.rightMoves = (↑) '' {q : ℚ | x < q} :=
  rightMoves_ofSets ..

theorem forall_leftMoves_toIGame {P : IGame → Prop} {x : ℝ} :
    (∀ y ∈ leftMoves (toIGame x), P y) ↔ ∀ q : ℚ, q < x → P q := by
  simp

theorem exists_leftMoves_toIGame {P : IGame → Prop} {x : ℝ} :
    (∃ y ∈ leftMoves (toIGame x), P y) ↔ ∃ q : ℚ, q < x ∧ P q := by
  simp

theorem forall_rightMoves_toIGame {P : IGame → Prop} {x : ℝ} :
    (∀ y ∈ rightMoves (toIGame x), P y) ↔ ∀ q : ℚ, x < q → P q := by
  simp

theorem exists_rightMoves_toIGame {P : IGame → Prop} {x : ℝ} :
    (∃ y ∈ rightMoves (toIGame x), P y) ↔ ∃ q : ℚ, x < q ∧ P q := by
  simp

theorem mem_leftMoves_toIGame_of_lt {q : ℚ} {x : ℝ} (h : q < x) :
    (q : IGame) ∈ x.toIGame.leftMoves := by
  simpa

theorem mem_rightMoves_toIGame_of_lt {q : ℚ} {x : ℝ} (h : x < q) :
    (q : IGame) ∈ x.toIGame.rightMoves := by
  simpa

@[simp]
theorem toIGame_neg (x : ℝ) : toIGame (-x) = -toIGame x := by
  simp_rw [toIGame_def, neg_ofSets, ofSets_inj, Set.neg_image (fun _ _ ↦ ratCast_neg _)]
  aesop (add simp [lt_neg, neg_lt])

theorem toIGame_ratCast_equiv (q : ℚ) : toIGame q ≈ q := by
  rw [AntisymmRel, le_iff_forall_lf, le_iff_forall_lf]
  refine ⟨⟨?_, fun x hx ↦ ?_⟩, ⟨fun x hx ↦ ?_, ?_⟩⟩
  · simp
  · obtain ⟨r, hr, hx⟩ := equiv_ratCast_of_mem_rightMoves_ratCast hx
    rw [hx.le_congr_left]
    apply lf_rightMove
    simpa
  · obtain ⟨r, hr, hx⟩ := equiv_ratCast_of_mem_leftMoves_ratCast hx
    rw [hx.le_congr_right]
    apply leftMove_lf
    simpa
  · simp

@[simp]
theorem ratCast_lt_toIGame {q : ℚ} {x : ℝ} : q < x.toIGame ↔ q < x := by
  obtain h | rfl | h := lt_trichotomy (q : ℝ) x
  · exact iff_of_true (Numeric.leftMove_lt (mem_leftMoves_toIGame_of_lt h)) h
  · simpa using (toIGame_ratCast_equiv q).not_gt
  · exact iff_of_false (Numeric.lt_rightMove (mem_rightMoves_toIGame_of_lt h)).asymm h.asymm

@[simp]
theorem toIGame_lt_ratCast {q : ℚ} {x : ℝ} : x.toIGame < q ↔ x < q := by
  obtain h | rfl | h := lt_trichotomy (q : ℝ) x
  · exact iff_of_false (Numeric.leftMove_lt (mem_leftMoves_toIGame_of_lt h)).asymm h.asymm
  · simpa using (toIGame_ratCast_equiv q).not_lt
  · exact iff_of_true (Numeric.lt_rightMove (mem_rightMoves_toIGame_of_lt h)) h

@[simp]
theorem ratCast_le_toIGame {q : ℚ} {x : ℝ} : q ≤ x.toIGame ↔ q ≤ x := by
  simp [← not_lt, ← Numeric.not_lt]

@[simp]
theorem toIGame_le_ratCast {q : ℚ} {x : ℝ} : x.toIGame ≤ q ↔ x ≤ q := by
  simp [← not_lt, ← Numeric.not_lt]

@[simp]
theorem ratCast_equiv_toIGame {q : ℚ} {x : ℝ} : (q : IGame) ≈ x.toIGame ↔ q = x := by
  simp [AntisymmRel, le_antisymm_iff]

@[simp]
theorem toIGame_equiv_ratCast {q : ℚ} {x : ℝ} : x.toIGame ≈ q ↔ x = q := by
  simp [AntisymmRel, le_antisymm_iff]

theorem toIGame_add_ratCast_equiv (x : ℝ) (q : ℚ) : x.toIGame + q ≈ (x + q).toIGame := by
  rw [AntisymmRel, le_iff_forall_lf, le_iff_forall_lf, forall_leftMoves_add, forall_rightMoves_add]
  simp_rw [forall_leftMoves_toIGame, forall_rightMoves_toIGame, Numeric.not_le]
  refine ⟨⟨⟨fun r hr ↦ ?_, ?_⟩, fun r hr ↦ ?_⟩, ⟨fun r hr ↦ ?_, ⟨fun r hr ↦ ?_, ?_⟩⟩⟩
  · rw [← (IGame.ratCast_add_equiv ..).lt_congr_left]
    simpa
  · intro y hy
    obtain ⟨r, hr, hy⟩ := equiv_ratCast_of_mem_leftMoves_ratCast hy
    rw [(add_congr_right hy).le_congr_right]
    rw [← ratCast_lt, ← add_lt_add_iff_left x] at hr
    obtain ⟨s, hs, hs'⟩ := exists_rat_btwn hr
    apply (lt_trans (b := (s : IGame)) _ _).not_le
    · rw [← IGame.lt_sub_iff_add_lt, ← (IGame.ratCast_sub_equiv ..).lt_congr_right]
      simpa [lt_sub_iff_add_lt]
    · simpa
  · rw [← IGame.lt_sub_iff_add_lt, ← (IGame.ratCast_sub_equiv ..).lt_congr_right]
    simpa [lt_sub_iff_add_lt]
  · rw [← IGame.sub_lt_iff_lt_add, ← (IGame.ratCast_sub_equiv ..).lt_congr_left]
    simpa [sub_lt_iff_lt_add]
  · rw [← (IGame.ratCast_add_equiv ..).lt_congr_right]
    simpa
  · intro y hy
    obtain ⟨r, hr, hy⟩ := equiv_ratCast_of_mem_rightMoves_ratCast hy
    rw [(add_congr_right hy).le_congr_left]
    rw [← ratCast_lt, ← add_lt_add_iff_left x] at hr
    obtain ⟨s, hs, hs'⟩ := exists_rat_btwn hr
    apply (lt_trans (b := (s : IGame)) _ _).not_le
    · simpa
    · rw [← IGame.sub_lt_iff_lt_add, ← (IGame.ratCast_sub_equiv ..).lt_congr_left]
      simpa [sub_lt_iff_lt_add]

theorem toIGame_ratCast_add_equiv (q : ℚ) (x : ℝ) : q + x.toIGame ≈ (q + x).toIGame := by
  simpa [add_comm] using toIGame_add_ratCast_equiv x q

theorem toIGame_add_equiv (x y : ℝ) : x.toIGame + y.toIGame ≈ (x + y).toIGame := by
  rw [AntisymmRel, le_iff_forall_lf, le_iff_forall_lf, forall_leftMoves_add, forall_rightMoves_add]
  simp_rw [forall_leftMoves_toIGame, forall_rightMoves_toIGame, Numeric.not_le]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ⟨?_, ⟨?_, ?_⟩⟩⟩ <;> intro q hq
  · rw [(toIGame_ratCast_add_equiv ..).lt_congr_left]
    simpa
  · rw [(toIGame_add_ratCast_equiv ..).lt_congr_left]
    simpa
  · rw [← lt_sub_iff_add_lt] at hq
    obtain ⟨r, hr, hr'⟩ := exists_rat_btwn hq
    rw [lt_sub_comm] at hr'
    obtain ⟨s, hs, hs'⟩ := exists_rat_btwn hr'
    trans r + s
    · apply add_lt_add <;> simpa
    · rw [add_comm, ← IGame.lt_sub_iff_add_lt, ← (ratCast_sub_equiv ..).lt_congr_right]
      simp_all [← Rat.cast_sub]
  · rw [← sub_lt_iff_lt_add] at hq
    obtain ⟨r, hr, hr'⟩ := exists_rat_btwn hq
    rw [sub_lt_comm] at hr
    obtain ⟨s, hs, hs'⟩ := exists_rat_btwn hr
    trans r + s
    · rw [add_comm, ← IGame.sub_lt_iff_lt_add, ← (ratCast_sub_equiv ..).lt_congr_left]
      simp_all [← Rat.cast_sub]
    · apply add_lt_add <;> simpa
  · rw [(toIGame_ratCast_add_equiv ..).lt_congr_right]
    simpa
  · rw [(toIGame_add_ratCast_equiv ..).lt_congr_right]
    simpa

theorem toIGame_sub_ratCast_equiv (x : ℝ) (q : ℚ) : x.toIGame - q ≈ (x - q).toIGame := by
  simpa using toIGame_add_ratCast_equiv x (-q)

theorem toIGame_ratCast_sub_equiv (q : ℚ) (x : ℝ) : q - x.toIGame ≈ (q - x).toIGame := by
  simpa using toIGame_ratCast_add_equiv q (-x)

theorem toIGame_sub_equiv (x y : ℝ) : x.toIGame - y.toIGame ≈ (x - y).toIGame := by
  simpa using toIGame_add_equiv x (-y)

theorem toIGame_mul_ratCast_equiv (x : ℝ) (q : ℚ) : x.toIGame * q ≈ (x * q).toIGame := by
  rw [AntisymmRel, le_iff_forall_lf, le_iff_forall_lf, forall_leftMoves_mul, forall_rightMoves_mul]
  simp_rw [forall_leftMoves_toIGame, forall_rightMoves_toIGame, Numeric.not_le]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ⟨?_, ⟨?_, ?_⟩⟩⟩
  · intro r hr y hy
    obtain ⟨s, hs, hy⟩ := equiv_ratCast_of_mem_leftMoves_ratCast hy
    unfold mulOption
    sorry
  · sorry
  · intro r h
    obtain hq | rfl | hq := lt_trichotomy q 0
    · rw [← lt_div_iff₀ (mod_cast hq)] at h
      rw [← Numeric.lt_div_iff (by simpa), ← (ratCast_div_equiv r hq).lt_congr_right]
      simpa
    · simp_all
    · rw [← lt_div_iff₀ (mod_cast hq)] at h
      rw [← Numeric.lt_div_iff (by simpa), ← (ratCast_div_equiv r hq).lt_congr_right]
      simpa


end Real
end
