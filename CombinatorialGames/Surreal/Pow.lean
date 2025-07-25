/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.Surreal.Real

/-!
# Surreal exponentiation

We define here the ω-map on games and on surreal numbers, representing exponentials with base `ω`.

TODO: define the normal form of a surreal number.
-/

open Set

theorem Set.image2_eq_range {α β γ : Type*} (f : α → β → γ) (s : Set α) (t : Set β) :
    Set.image2 f s t = Set.range (fun x : s × t ↦ f x.1 x.2) := by
  aesop

namespace IGame

/-- The ω-map on games, which is defined so that `ω^ {s | t}ᴵ = {0, r * ω^ a | r * ω^ b}` for
`a ∈ s`, `b ∈ t`, and `r` ranging over positive dyadic rationals.

The standard definition in the literature instead has `r` ranging over positive reals,
but this makes no difference as to the equivalence class of the games. -/
noncomputable def opow (x : IGame) : IGame :=
  {insert 0 (range (fun y : Ioi (0 : Dyadic) × x.leftMoves ↦ y.1 * opow y.2)) |
    range (fun y : Ioi (0 : Dyadic) × x.rightMoves ↦ y.1 * opow y.2)}ᴵ
termination_by x
decreasing_by igame_wf

prefix:75 "ω^ " => opow

theorem leftMoves_opow (x : IGame) : leftMoves (ω^ x) =
    insert 0 (image2 (fun r y ↦ ↑r * ω^ y) (Ioi (0 : Dyadic)) x.leftMoves) := by
  rw [opow, leftMoves_ofSets, Set.image2_eq_range]

theorem rightMoves_opow (x : IGame) : rightMoves (ω^ x) =
    image2 (fun r y ↦ ↑r * ω^ y) (Ioi (0 : Dyadic)) x.rightMoves := by
  rw [opow, rightMoves_ofSets, Set.image2_eq_range]

@[simp]
theorem forall_leftMoves_opow {x : IGame} {P : IGame → Prop} : (∀ y ∈ leftMoves (ω^ x), P y) ↔
    P 0 ∧ ∀ r : Dyadic, 0 < r → ∀ y ∈ x.leftMoves, P (r * ω^ y) := by
  rw [leftMoves_opow, forall_mem_insert, forall_mem_image2]
  rfl

@[simp]
theorem forall_rightMoves_opow {x : IGame} {P : IGame → Prop} : (∀ y ∈ rightMoves (ω^ x), P y) ↔
    ∀ r : Dyadic, 0 < r → ∀ y ∈ x.rightMoves, P (r * ω^ y) := by
  rw [rightMoves_opow]
  exact forall_mem_image2

@[simp]
theorem exists_leftMoves_opow {x : IGame} {P : IGame → Prop} : (∃ y ∈ leftMoves (ω^ x), P y) ↔
    P 0 ∨ ∃ r : Dyadic, 0 < r ∧ ∃ y ∈ x.leftMoves, P (r * ω^ y) := by
  rw [leftMoves_opow, exists_mem_insert, exists_mem_image2]
  rfl

@[simp]
theorem exists_rightMoves_opow {x : IGame} {P : IGame → Prop} : (∃ y ∈ rightMoves (ω^ x), P y) ↔
    ∃ r : Dyadic, 0 < r ∧ ∃ y ∈ x.rightMoves, P (r * ω^ y) := by
  rw [rightMoves_opow]
  exact exists_mem_image2

@[simp]
theorem zero_mem_leftMoves_opow (x : IGame) : 0 ∈ leftMoves (ω^ x) := by
  simp [leftMoves_opow]

theorem mul_opow_mem_leftMoves_opow {x y : IGame} {r : Dyadic} (hr : 0 ≤ r)
    (hy : y ∈ x.leftMoves) : r * ω^ y ∈ leftMoves (ω^ x) := by
  obtain rfl | hr := hr.eq_or_lt
  · simp
  · rw [leftMoves_opow]
    apply mem_insert_of_mem
    use r, hr, y, hy

theorem mul_opow_mem_rightMoves_opow {x y : IGame} {r : Dyadic} (hr : 0 < r)
    (hy : y ∈ x.rightMoves) : r * ω^ y ∈ rightMoves (ω^ x) := by
  rw [rightMoves_opow]
  use r, hr, y, hy

theorem natCast_mul_opow_mem_leftMoves_opow {x y : IGame} (n : ℕ) (hy : y ∈ x.leftMoves) :
    n * ω^ y ∈ leftMoves (ω^ x) := by
  simpa using mul_opow_mem_leftMoves_opow n.cast_nonneg hy

theorem natCast_mul_opow_mem_rightMoves_opow {x y : IGame} {n : ℕ} (hn : 0 < n)
    (hy : y ∈ x.rightMoves) : n * ω^ y ∈ rightMoves (ω^ x) := by
  simpa using mul_opow_mem_rightMoves_opow (n.cast_pos.2 hn) hy

theorem opow_mem_leftMoves_opow {x y : IGame} (hy : y ∈ x.leftMoves) :
    ω^ y ∈ leftMoves (ω^ x) := by
  simpa using natCast_mul_opow_mem_leftMoves_opow 1 hy

theorem opow_mem_rightMoves_opow {x y : IGame} (hy : y ∈ x.rightMoves) :
    ω^ y ∈ rightMoves (ω^ x) := by
  simpa using natCast_mul_opow_mem_rightMoves_opow one_pos hy

theorem zero_lf_opow (x : IGame) : 0 ⧏ ω^ x :=
  leftMove_lf (zero_mem_leftMoves_opow x)

private theorem opow_pos' (x : IGame) [Numeric (ω^ x)] : 0 < ω^ x := by
  simpa using zero_lf_opow x

@[simp]
theorem opow_zero : ω^ 0 = 1 := by
  ext <;> simp [leftMoves_opow, rightMoves_opow]

namespace Numeric

variable {x y : IGame} [Numeric x] [Numeric y]

private theorem opow_strictMono_aux {x y : IGame} [Numeric x] [Numeric y]
    [Numeric (ω^ x)] [Numeric (ω^ y)] :
    (x < y → ∀ {r : ℝ}, 0 < r → r * ω^ x < ω^ y) ∧ (x ≤ y → ω^ x ≤ ω^ y) := by
  refine ⟨fun hxy r hr ↦ ?_, fun hxy ↦ ?_⟩
  · obtain (⟨z, hz, hxz⟩ | ⟨z, hz, hzy⟩) := lf_iff_exists_le.1 hxy.not_ge
    · have := Numeric.of_mem_leftMoves hz
      have := Numeric.of_mem_leftMoves (opow_mem_leftMoves_opow hz)
      apply ((Numeric.mul_le_mul_left (mod_cast hr)).2 (opow_strictMono_aux.2 hxz)).trans_lt
      obtain ⟨n, hn⟩ := exists_nat_gt r
      exact ((Numeric.mul_lt_mul_right (opow_pos' z)).2 (Real.toIGame_lt_natCast.2 hn)).trans
        (Numeric.leftMove_lt (natCast_mul_opow_mem_leftMoves_opow n hz))
    · have := Numeric.of_mem_rightMoves hz
      have := Numeric.of_mem_rightMoves (opow_mem_rightMoves_opow hz)
      apply (opow_strictMono_aux.2 hzy).trans_lt'
      rw [← Numeric.lt_div_iff' (mod_cast hr), IGame.div_eq_mul_inv, mul_comm,
        ← (Numeric.mul_congr_left r.toIGame_inv_equiv).lt_congr_right]
      obtain ⟨q, hq, hq'⟩ := exists_dyadic_btwn (inv_pos.2 hr)
      apply (Numeric.lt_rightMove (mul_opow_mem_rightMoves_opow (mod_cast hq) hz)).trans
      rw [Numeric.mul_lt_mul_right (opow_pos' z)]
      simpa
  · rw [le_iff_forall_lf, forall_leftMoves_opow, forall_rightMoves_opow]
    refine ⟨⟨zero_lf_opow _, ?_⟩, ?_⟩ <;> intro r hr z hz
    · have := Numeric.of_mem_leftMoves hz
      have := Numeric.of_mem_leftMoves (opow_mem_leftMoves_opow hz)
      rw [← (Numeric.mul_congr_left (Real.toIGame_dyadic_equiv r)).le_congr_right]
      exact (opow_strictMono_aux.1 ((Numeric.leftMove_lt hz).trans_le hxy) (mod_cast hr)).not_ge
    · have := Numeric.of_mem_rightMoves hz
      have := Numeric.of_mem_rightMoves (opow_mem_rightMoves_opow hz)
      apply not_le_of_gt
      rw [← (Numeric.mul_congr_left (Real.toIGame_dyadic_equiv r)).lt_congr_right,
        ← Numeric.div_lt_iff' (mod_cast hr), IGame.div_eq_mul_inv, mul_comm,
        ← (Numeric.mul_congr_left (Real.toIGame_inv_equiv _)).lt_congr_left]
      apply opow_strictMono_aux.1 (hxy.trans_lt (Numeric.lt_rightMove hz))
      simpa
termination_by (x, y)
decreasing_by igame_wf

protected instance opow (x : IGame) [Numeric x] : Numeric (ω^ x) := by
  rw [numeric_def]
  simp_rw [forall_leftMoves_opow, forall_rightMoves_opow]
  refine ⟨⟨fun r hr y hy ↦ ?_, fun r hr y hy s hs z hz ↦ ?_⟩,
    ⟨.zero, fun r hr y hy ↦ ?_⟩, fun r hr y hy ↦ ?_⟩
  all_goals
    first | have := Numeric.of_mem_leftMoves hy | have := Numeric.of_mem_rightMoves hy
    have := Numeric.opow y
  · exact Numeric.mul_pos (mod_cast hr) (opow_pos' y)
  · have := Numeric.of_mem_rightMoves hz
    have := Numeric.opow z
    rw [← Numeric.div_lt_iff' (mod_cast hs), ← Surreal.mk_lt_mk]
    dsimp
    simp_rw [div_eq_inv_mul, ← mul_assoc, Surreal.mk_dyadic, ← Real.toSurreal_ratCast,
      ← Real.toSurreal_inv, ← Real.toSurreal_mul]
    apply opow_strictMono_aux.1 (Numeric.leftMove_lt_rightMove hy hz) (_root_.mul_pos ..) <;>
      simpa
  all_goals infer_instance
termination_by x
decreasing_by igame_wf

@[simp]
theorem opow_pos (x : IGame) [Numeric x] : 0 < ω^ x := opow_pos' x

theorem mul_opow_lt_opow (r : ℝ) (h : x < y) : r * ω^ x < ω^ y := by
  obtain hr | hr := le_or_gt r 0
  · apply (Numeric.mul_nonpos_of_nonpos_of_nonneg _ (opow_pos x).le).trans_lt (opow_pos y)
    simpa
  · exact opow_strictMono_aux.1 h hr

theorem mul_opow_lt_opow' (r : Dyadic) (h : x < y) : r * ω^ x < ω^ y := by
  rw [← (mul_congr_left (Real.toIGame_dyadic_equiv r)).lt_congr_left]
  exact mul_opow_lt_opow r h

theorem opow_lt_mul_opow {r : ℝ} (hr : 0 < r) (h : x < y) : ω^ x < r * ω^ y := by
  rw [← Numeric.div_lt_iff' (mod_cast hr), IGame.div_eq_mul_inv, mul_comm,
    ← (Numeric.mul_congr_left (Real.toIGame_inv_equiv r)).lt_congr_left]
  exact mul_opow_lt_opow _ h

theorem opow_lt_mul_opow' {r : Dyadic} (hr : 0 < r) (h : x < y) : ω^ x < r * ω^ y := by
  rw [← (mul_congr_left (Real.toIGame_dyadic_equiv r)).lt_congr_right]
  exact opow_lt_mul_opow (mod_cast hr) h

theorem mul_opow_lt_mul_opow (r : ℝ) {s : ℝ} (hs : 0 < s) (h : x < y) : r * ω^ x < s * ω^ y := by
  rw [← Numeric.div_lt_iff' (mod_cast hs), ← Surreal.mk_lt_mk]
  dsimp
  rw [div_eq_mul_inv, mul_comm, ← mul_assoc, ← Real.toSurreal_inv, ← Real.toSurreal_mul]
  exact mul_opow_lt_opow _ h

theorem mul_opow_lt_mul_opow' (r : Dyadic) {s : Dyadic} (hs : 0 < s) (h : x < y) :
    r * ω^ x < s * ω^ y := by
  rw [← (mul_congr_left (Real.toIGame_dyadic_equiv r)).lt_congr_left,
    ← (mul_congr_left (Real.toIGame_dyadic_equiv s)).lt_congr_right]
  exact mul_opow_lt_mul_opow r (mod_cast hs) h

@[simp]
theorem opow_lt_opow : ω^ x < ω^ y ↔ x < y := by
  constructor
  · contrapose
    simp_rw [Numeric.not_lt]
    exact opow_strictMono_aux.2
  · simpa using mul_opow_lt_opow' 1

@[simp]
theorem opow_le_opow : ω^ x ≤ ω^ y ↔ x ≤ y := by
  rw [← Numeric.not_lt, opow_lt_opow, Numeric.not_lt]

theorem opow_congr (h : x ≈ y) : ω^ x ≈ ω^ y := by
  simp_all [AntisymmRel]

theorem opow_add (x y : IGame) [Numeric x] [Numeric y] : ω^ (x + y) ≈ ω^ x * ω^ y := by
  rw [AntisymmRel, le_iff_forall_lf, le_iff_forall_lf]
  simp only [forall_leftMoves_opow, forall_rightMoves_opow, forall_and,
    forall_leftMoves_add, forall_rightMoves_add, forall_leftMoves_mul, forall_rightMoves_mul]
  repeat any_goals constructor
  on_goal 1 => exact (mul_pos (opow_pos _) (opow_pos _)).not_ge
  on_goal 7 => simp
  all_goals
    intro r hr z hz
    first | have := Numeric.of_mem_leftMoves hz | have := Numeric.of_mem_rightMoves hz
  · rw [(mul_congr_right (opow_add z y)).le_congr_right, ← (mul_assoc_equiv ..).le_congr_right,
      Numeric.mul_le_mul_right (opow_pos _), Numeric.not_le]
    exact mul_opow_lt_opow' r (Numeric.leftMove_lt hz)
  · rw [(mul_congr_right (opow_add x z)).le_congr_right, mul_comm (r : IGame),
      (mul_assoc_equiv ..).le_congr_right, Numeric.mul_le_mul_left (opow_pos _), mul_comm]
    exact (mul_opow_lt_opow' r (Numeric.leftMove_lt hz)).not_ge
  · rw [mulOption_zero_left, mul_comm (r : IGame), ← (mul_assoc_equiv ..).le_congr_left, mul_comm,
      ← (mul_congr_right (opow_add x z)).le_congr_left]
    exact (opow_lt_mul_opow' hr (add_left_strictMono (Numeric.lt_rightMove hz))).not_ge
  · intro s hs w hw
    have := Numeric.of_mem_rightMoves hw
    rw [mulOption, Numeric.not_le]
    apply add_lt_add
    · rw [(mul_assoc_equiv ..).lt_congr_right, ← (mul_congr_right (opow_add z y)).lt_congr_right]
      apply opow_lt_mul_opow' hr (add_right_strictMono _)
      exact (Numeric.leftMove_lt hz)
    · sorry
  · simp [mulOption]
    sorry
  · intro s hs w hw
    sorry
  · simp [mulOption]
    sorry
  · simp [mulOption]
    sorry
  · intro s hs w hw
    sorry
termination_by (x, y)
decreasing_by igame_wf

end Numeric
end IGame
