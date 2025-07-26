/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.Surreal.Real

/-!
# Surreal exponentiation

We define here the ω-map on games and on surreal numbers, representing exponentials with base `ω`.

## Todo

- Prove that `ω^ x` matches ordinal exponentiation for ordinal `x`.
- Define commensurate surreals and prove properties relating to `ω^ x`.
- Define the normal form of a surreal number.
-/

open Set

-- TOOD: upstream
theorem Set.image2_eq_range {α β γ : Type*} (f : α → β → γ) (s : Set α) (t : Set β) :
    Set.image2 f s t = Set.range (fun x : s × t ↦ f x.1 x.2) := by
  aesop

/-- A typeclass for the the `ω^` notation. -/
class Wpow (α : Type*) where
  wpow : α → α

prefix:75 "ω^ " => Wpow.wpow

noncomputable section
namespace IGame

/-- The ω-map on games, which is defined so that `ω^ {s | t}ᴵ = {0, r * ω^ a | r * ω^ b}` for
`a ∈ s`, `b ∈ t`, and `r` ranging over positive dyadic rationals.

The standard definition in the literature instead has `r` ranging over positive reals,
but this makes no difference as to the equivalence class of the games. -/
private def wpow (x : IGame) : IGame :=
  {insert 0 (range (fun y : Ioi (0 : Dyadic) × x.leftMoves ↦ y.1 * wpow y.2)) |
    range (fun y : Ioi (0 : Dyadic) × x.rightMoves ↦ y.1 * wpow y.2)}ᴵ
termination_by x
decreasing_by igame_wf

instance : Wpow IGame where
  wpow := wpow

theorem wpow_def (x : IGame) : ω^ x =
    {insert 0 (image2 (fun r y ↦ ↑r * ω^ (y : IGame)) (Ioi (0 : Dyadic)) x.leftMoves) |
      image2 (fun r y ↦ ↑r * ω^ y) (Ioi (0 : Dyadic)) x.rightMoves}ᴵ := by
  change wpow _ = _
  rw [wpow]
  simp_rw [Set.image2_eq_range]
  rfl

theorem leftMoves_wpow (x : IGame) : leftMoves (ω^ x) =
    insert 0 (image2 (fun r y ↦ ↑r * ω^ (y : IGame)) (Ioi (0 : Dyadic)) x.leftMoves) := by
  rw [wpow_def, leftMoves_ofSets, Set.image2_eq_range]

theorem rightMoves_wpow (x : IGame) : rightMoves (ω^ x) =
    image2 (fun r y ↦ ↑r * ω^ (y : IGame)) (Ioi (0 : Dyadic)) x.rightMoves := by
  rw [wpow_def, rightMoves_ofSets, Set.image2_eq_range]

@[simp]
theorem forall_leftMoves_wpow {x : IGame} {P : IGame → Prop} : (∀ y ∈ leftMoves (ω^ x), P y) ↔
    P 0 ∧ ∀ r : Dyadic, 0 < r → ∀ y ∈ x.leftMoves, P (r * ω^ y) := by
  rw [leftMoves_wpow, forall_mem_insert, forall_mem_image2]
  rfl

@[simp]
theorem forall_rightMoves_wpow {x : IGame} {P : IGame → Prop} : (∀ y ∈ rightMoves (ω^ x), P y) ↔
    ∀ r : Dyadic, 0 < r → ∀ y ∈ x.rightMoves, P (r * ω^ y) := by
  rw [rightMoves_wpow]
  exact forall_mem_image2

@[simp]
theorem exists_leftMoves_wpow {x : IGame} {P : IGame → Prop} : (∃ y ∈ leftMoves (ω^ x), P y) ↔
    P 0 ∨ ∃ r : Dyadic, 0 < r ∧ ∃ y ∈ x.leftMoves, P (r * ω^ y) := by
  rw [leftMoves_wpow, exists_mem_insert, exists_mem_image2]
  rfl

@[simp]
theorem exists_rightMoves_wpow {x : IGame} {P : IGame → Prop} : (∃ y ∈ rightMoves (ω^ x), P y) ↔
    ∃ r : Dyadic, 0 < r ∧ ∃ y ∈ x.rightMoves, P (r * ω^ y) := by
  rw [rightMoves_wpow]
  exact exists_mem_image2

@[simp]
theorem zero_mem_leftMoves_wpow (x : IGame) : 0 ∈ leftMoves (ω^ x) := by
  simp [leftMoves_wpow]

theorem mul_wpow_mem_leftMoves_wpow {x y : IGame} {r : Dyadic} (hr : 0 ≤ r)
    (hy : y ∈ x.leftMoves) : r * ω^ y ∈ leftMoves (ω^ x) := by
  obtain rfl | hr := hr.eq_or_lt
  · simp
  · rw [leftMoves_wpow]
    apply mem_insert_of_mem
    use r, hr, y, hy

theorem mul_wpow_mem_rightMoves_wpow {x y : IGame} {r : Dyadic} (hr : 0 < r)
    (hy : y ∈ x.rightMoves) : r * ω^ y ∈ rightMoves (ω^ x) := by
  rw [rightMoves_wpow]
  use r, hr, y, hy

theorem natCast_mul_wpow_mem_leftMoves_wpow {x y : IGame} (n : ℕ) (hy : y ∈ x.leftMoves) :
    n * ω^ y ∈ leftMoves (ω^ x) := by
  simpa using mul_wpow_mem_leftMoves_wpow n.cast_nonneg hy

theorem natCast_mul_wpow_mem_rightMoves_wpow {x y : IGame} {n : ℕ} (hn : 0 < n)
    (hy : y ∈ x.rightMoves) : n * ω^ y ∈ rightMoves (ω^ x) := by
  simpa using mul_wpow_mem_rightMoves_wpow (n.cast_pos.2 hn) hy

theorem wpow_mem_leftMoves_wpow {x y : IGame} (hy : y ∈ x.leftMoves) :
    ω^ y ∈ leftMoves (ω^ x) := by
  simpa using natCast_mul_wpow_mem_leftMoves_wpow 1 hy

theorem wpow_mem_rightMoves_wpow {x y : IGame} (hy : y ∈ x.rightMoves) :
    ω^ y ∈ rightMoves (ω^ x) := by
  simpa using natCast_mul_wpow_mem_rightMoves_wpow one_pos hy

theorem zero_lf_wpow (x : IGame) : 0 ⧏ ω^ x :=
  leftMove_lf (zero_mem_leftMoves_wpow x)

private theorem wpow_pos' (x : IGame) [Numeric (ω^ x)] : 0 < ω^ x := by
  simpa using zero_lf_wpow x

@[simp]
theorem wpow_zero : ω^ (0 : IGame) = 1 := by
  ext <;> simp [leftMoves_wpow, rightMoves_wpow]

namespace Numeric

variable {x y z w : IGame} [Numeric x] [Numeric y] [Numeric z] [Numeric w]

private theorem wpow_strictMono_aux {x y : IGame} [Numeric x] [Numeric y]
    [Numeric (ω^ x)] [Numeric (ω^ y)] :
    (x < y → ∀ {r : ℝ}, 0 < r → r * ω^ x < ω^ y) ∧ (x ≤ y → ω^ x ≤ ω^ y) := by
  refine ⟨fun hxy r hr ↦ ?_, fun hxy ↦ ?_⟩
  · obtain (⟨z, hz, hxz⟩ | ⟨z, hz, hzy⟩) := lf_iff_exists_le.1 hxy.not_ge
    · have := Numeric.of_mem_leftMoves hz
      have := Numeric.of_mem_leftMoves (wpow_mem_leftMoves_wpow hz)
      apply ((Numeric.mul_le_mul_left (mod_cast hr)).2 (wpow_strictMono_aux.2 hxz)).trans_lt
      obtain ⟨n, hn⟩ := exists_nat_gt r
      exact ((Numeric.mul_lt_mul_right (wpow_pos' z)).2 (mod_cast hn)).trans
        (Numeric.leftMove_lt (natCast_mul_wpow_mem_leftMoves_wpow n hz))
    · have := Numeric.of_mem_rightMoves hz
      have := Numeric.of_mem_rightMoves (wpow_mem_rightMoves_wpow hz)
      apply (wpow_strictMono_aux.2 hzy).trans_lt'
      rw [← Numeric.lt_div_iff' (mod_cast hr), IGame.div_eq_mul_inv, mul_comm,
        ← (Numeric.mul_congr_left r.toIGame_inv_equiv).lt_congr_right]
      obtain ⟨q, hq, hq'⟩ := exists_dyadic_btwn (inv_pos.2 hr)
      apply (Numeric.lt_rightMove (mul_wpow_mem_rightMoves_wpow (mod_cast hq) hz)).trans
      rw [Numeric.mul_lt_mul_right (wpow_pos' z)]
      simpa
  · rw [le_iff_forall_lf, forall_leftMoves_wpow, forall_rightMoves_wpow]
    refine ⟨⟨zero_lf_wpow _, ?_⟩, ?_⟩ <;> intro r hr z hz
    · have := Numeric.of_mem_leftMoves hz
      have := Numeric.of_mem_leftMoves (wpow_mem_leftMoves_wpow hz)
      rw [← (Numeric.mul_congr_left (Real.toIGame_dyadic_equiv r)).le_congr_right]
      exact (wpow_strictMono_aux.1 ((Numeric.leftMove_lt hz).trans_le hxy) (mod_cast hr)).not_ge
    · have := Numeric.of_mem_rightMoves hz
      have := Numeric.of_mem_rightMoves (wpow_mem_rightMoves_wpow hz)
      have hr' : 0 < (r : ℝ)⁻¹ := by simpa
      rw [← Surreal.mk_le_mk, Surreal.mk_mul, ← le_div_iff₀' (by simpa), div_eq_inv_mul]
      simpa [← Surreal.mk_lt_mk] using
        wpow_strictMono_aux.1 (hxy.trans_lt (Numeric.lt_rightMove hz)) hr'
termination_by (x, y)
decreasing_by igame_wf

protected instance wpow (x : IGame) [Numeric x] : Numeric (ω^ x) := by
  rw [numeric_def]
  simp_rw [forall_leftMoves_wpow, forall_rightMoves_wpow]
  refine ⟨⟨fun r hr y hy ↦ ?_, fun r hr y hy s hs z hz ↦ ?_⟩,
    ⟨.zero, fun r hr y hy ↦ ?_⟩, fun r hr y hy ↦ ?_⟩
  all_goals
    first | have := Numeric.of_mem_leftMoves hy | have := Numeric.of_mem_rightMoves hy
    have := Numeric.wpow y
  · exact Numeric.mul_pos (mod_cast hr) (wpow_pos' y)
  · have := Numeric.of_mem_rightMoves hz
    have := Numeric.wpow z
    rw [← Numeric.div_lt_iff' (mod_cast hs), ← Surreal.mk_lt_mk]
    dsimp
    simp_rw [div_eq_inv_mul, ← mul_assoc, Surreal.mk_dyadic,
      ← Real.toSurreal_ratCast, ← Real.toSurreal_inv, ← Real.toSurreal_mul]
    apply wpow_strictMono_aux.1 (Numeric.leftMove_lt_rightMove hy hz) (mul_pos ..) <;> simpa
  all_goals infer_instance
termination_by x
decreasing_by igame_wf

@[simp]
theorem wpow_pos (x : IGame) [Numeric x] : 0 < ω^ x := wpow_pos' x

theorem mul_wpow_lt_wpow (r : ℝ) (h : x < y) : r * ω^ x < ω^ y := by
  obtain hr | hr := le_or_gt r 0
  · apply (Numeric.mul_nonpos_of_nonpos_of_nonneg _ (wpow_pos x).le).trans_lt (wpow_pos y)
    simpa
  · exact wpow_strictMono_aux.1 h hr

/-- A version of `mul_wpow_lt_wpow` stated using dyadic rationals. -/
theorem mul_wpow_lt_wpow' (r : Dyadic) (h : x < y) : r * ω^ x < ω^ y := by
  simpa [← Surreal.mk_lt_mk] using mul_wpow_lt_wpow r h

theorem wpow_lt_mul_wpow {r : ℝ} (hr : 0 < r) (h : x < y) : ω^ x < r * ω^ y := by
  rw [← Numeric.div_lt_iff' (mod_cast hr), IGame.div_eq_mul_inv, mul_comm]
  simpa [← Surreal.mk_lt_mk] using mul_wpow_lt_wpow (r⁻¹) h

/-- A version of `wpow_lt_mul_wpow` stated using dyadic rationals. -/
theorem wpow_lt_mul_wpow' {r : Dyadic} (hr : 0 < r) (h : x < y) : ω^ x < r * ω^ y := by
  have hr : (0 : ℝ) < r := by simpa
  simpa [← Surreal.mk_lt_mk] using wpow_lt_mul_wpow hr h

theorem mul_wpow_lt_mul_wpow (r : ℝ) {s : ℝ} (hs : 0 < s) (h : x < y) : r * ω^ x < s * ω^ y := by
  rw [← Numeric.div_lt_iff' (mod_cast hs), ← Surreal.mk_lt_mk]
  dsimp
  rw [div_eq_mul_inv, mul_comm, ← mul_assoc, ← Real.toSurreal_inv, ← Real.toSurreal_mul]
  exact mul_wpow_lt_wpow _ h

/-- A version of `mul_wpow_lt_mul_wpow` stated using dyadic rationals. -/
theorem mul_wpow_lt_mul_wpow' (r : Dyadic) {s : Dyadic} (hs : 0 < s) (h : x < y) :
    r * ω^ x < s * ω^ y := by
  have hs : (0 : ℝ) < s := by simpa
  simpa [← Surreal.mk_lt_mk] using mul_wpow_lt_mul_wpow r hs h

theorem mul_wpow_add_mul_wpow_lt_mul_wpow (r s : ℝ) {t : ℝ} (ht : 0 < t)
     (hx : x < z) (hy : y < z) : r * ω^ x + s * ω^ y < t * ω^ z := by
  have h : 0 < t / 2 := by simpa
  apply (add_lt_add (mul_wpow_lt_mul_wpow r h hx) (mul_wpow_lt_mul_wpow s h hy)).trans_le
  simp [← Surreal.mk_le_mk, ← add_mul]

/-- A version of `mul_wpow_add_mul_wpow_lt_mul_wpow` stated using dyadic rationals. -/
theorem mul_wpow_add_mul_wpow_lt_mul_wpow' (r s : Dyadic) {t : Dyadic} (ht : 0 < t)
    (hx : x < z) (hy : y < z) : r * ω^ x + s * ω^ y < t * ω^ z := by
  have ht : (0 : ℝ) < t := by simpa
  simpa [← Surreal.mk_lt_mk] using mul_wpow_add_mul_wpow_lt_mul_wpow r s ht hx hy

theorem mul_wpow_lt_mul_wpow_add_mul_wpow (r : ℝ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hx : x < y) (hy : x < z) : r * ω^ x < s * ω^ y + t * ω^ z := by
  apply (add_lt_add (mul_wpow_lt_mul_wpow (r/2) hs hx) (mul_wpow_lt_mul_wpow (r/2) ht hy)).trans_le'
  simp [← Surreal.mk_le_mk, ← add_mul]

/-- A version of `mul_wpow_lt_mul_wpow_add_mul_wpow` stated using dyadic rationals. -/
theorem mul_wpow_lt_mul_wpow_add_mul_wpow' (r : Dyadic) {s t : Dyadic} (hs : 0 < s) (ht : 0 < t)
    (hx : x < y) (hy : x < z) : r * ω^ x < s * ω^ y + t * ω^ z := by
  have hs : (0 : ℝ) < s := by simpa
  have ht : (0 : ℝ) < t := by simpa
  simpa [← Surreal.mk_lt_mk] using mul_wpow_lt_mul_wpow_add_mul_wpow r hs ht hx hy

@[simp]
theorem wpow_lt_wpow : ω^ x < ω^ y ↔ x < y := by
  constructor
  · contrapose
    simp_rw [Numeric.not_lt]
    exact wpow_strictMono_aux.2
  · simpa using mul_wpow_lt_wpow' 1

@[simp]
theorem wpow_le_wpow : ω^ x ≤ ω^ y ↔ x ≤ y := by
  rw [← Numeric.not_lt, wpow_lt_wpow, Numeric.not_lt]

theorem wpow_congr (h : x ≈ y) : ω^ x ≈ ω^ y := by
  simp_all [AntisymmRel]

private theorem mulOption_lt_wpow {r s : Dyadic} (hr : 0 < r) (hs : 0 < s)
    (h₁ : x < z) (h₂ : y < w) (IH₁ : ω^ (x + w) ≈ ω^ x * ω^ w)
    (IH₂ : ω^ (z + y) ≈ ω^ z * ω^ y) (IH₃ : ω^ (z + w) ≈ ω^ z * ω^ w) :
    mulOption (ω^ x) (ω^ y) (r * ω^ z) (s * ω^ w) < ω^ (x + y) := by
  apply IGame.sub_lt_iff_lt_add.2
  have H : r * ω^ (z + y) + s * ω^ (x + w) < ω^ (x + y) + ↑(r * s) * ω^ (z + w) := by
    apply (mul_wpow_add_mul_wpow_lt_mul_wpow' ..).trans (lt_add_of_pos_left ..) <;> simp_all
  rw [← Surreal.mk_lt_mk, ← Surreal.mk_eq_mk] at *
  convert H using 1 <;> simp_all <;> ring_nf

private theorem mulOption_lt_wpow' {r s : Dyadic} (hr : 0 < r) (hs : 0 < s)
    (h₁ : z < x) (h₂ : w < y) (IH₁ : ω^ (x + w) ≈ ω^ x * ω^ w)
    (IH₂ : ω^ (z + y) ≈ ω^ z * ω^ y) (IH₃ : ω^ (z + w) ≈ ω^ z * ω^ w) :
    mulOption (ω^ x) (ω^ y) (r * ω^ z) (s * ω^ w) < ω^ (x + y) := by
  apply IGame.sub_lt_iff_lt_add.2
  have H : r * ω^ (z + y) + s * ω^ (x + w) < (1 : Dyadic) * ω^ (x + y) + ↑(r * s) * ω^ (z + w) := by
    apply (mul_wpow_add_mul_wpow_lt_mul_wpow' ..).trans (lt_add_of_pos_right ..) <;> simp_all
  rw [← Surreal.mk_lt_mk, ← Surreal.mk_eq_mk] at *
  convert H using 1 <;> simp_all <;> ring_nf

private theorem wpow_lt_mulOption {r s : Dyadic} (hr : 0 < r) (hs : 0 < s)
    (h₁ : x < z) (h₂ : w < y) (IH₁ : ω^ (z + y) ≈ ω^ z * ω^ y) (IH₂ : ω^ (z + w) ≈ ω^ z * ω^ w) :
    ω^(x + y) < mulOption (ω^ x) (ω^ y) (r * ω^ z) (s * ω^ w) := by
  apply IGame.lt_sub_iff_add_lt.2
  have H : (1 : Dyadic) * ω^ (x + y) + ↑(r * s) * ω^ (z + w) < r * ω^ (z + y) + s * ω^ x * ω^ w := by
    apply (mul_wpow_add_mul_wpow_lt_mul_wpow' ..).trans (lt_add_of_pos_right ..) <;> simp_all
  rw [← Surreal.mk_lt_mk, ← Surreal.mk_eq_mk] at *
  convert H using 1 <;> simp_all <;> ring_nf

theorem wpow_add_equiv (x y : IGame) [Numeric x] [Numeric y] : ω^ (x + y) ≈ ω^ x * ω^ y := by
  rw [AntisymmRel, le_iff_forall_lf, le_iff_forall_lf]
  simp only [forall_leftMoves_wpow, forall_rightMoves_wpow, forall_and,
    forall_leftMoves_add, forall_rightMoves_add, forall_leftMoves_mul, forall_rightMoves_mul]
  repeat any_goals constructor
  on_goal 1 => exact (Numeric.mul_pos (wpow_pos _) (wpow_pos _)).not_ge
  on_goal 7 => simp
  all_goals
    intro r hr z hz
    first | have := Numeric.of_mem_leftMoves hz | have := Numeric.of_mem_rightMoves hz
  any_goals
    intro s hs w hw
    first | have := Numeric.of_mem_leftMoves hw | have := Numeric.of_mem_rightMoves hw
  all_goals apply not_le_of_gt
  · rw [(mul_congr_right (wpow_add_equiv ..)).lt_congr_left, ← (mul_assoc_equiv ..).lt_congr_left,
      Numeric.mul_lt_mul_right (wpow_pos _)]
    exact mul_wpow_lt_wpow' r (Numeric.leftMove_lt hz)
  · rw [(mul_congr_right (wpow_add_equiv ..)).lt_congr_left, mul_comm (r : IGame),
      (mul_assoc_equiv ..).lt_congr_left, Numeric.mul_lt_mul_left (wpow_pos _), mul_comm]
    exact mul_wpow_lt_wpow' r (Numeric.leftMove_lt hz)
  · rw [mulOption_zero_left, mul_comm (r : IGame), ← (mul_assoc_equiv ..).lt_congr_right, mul_comm,
      ← (mul_congr_right (wpow_add_equiv ..)).lt_congr_right]
    exact wpow_lt_mul_wpow' hr (add_left_strictMono (Numeric.lt_rightMove hz))
  · rw [mulOption_comm, add_comm]
    apply wpow_lt_mulOption hs hr (Numeric.lt_rightMove hw) (Numeric.leftMove_lt hz) <;>
      rw [add_comm, mul_comm] <;> exact wpow_add_equiv ..
  · rw [mulOption_zero_right, (mul_assoc_equiv ..).lt_congr_right,
      ← (mul_congr_right (wpow_add_equiv ..)).lt_congr_right]
    exact wpow_lt_mul_wpow' hr (add_right_strictMono (Numeric.lt_rightMove hz))
  · exact wpow_lt_mulOption hr hs (Numeric.lt_rightMove hz) (Numeric.leftMove_lt hw)
      (wpow_add_equiv ..) (wpow_add_equiv ..)
  · rw [mulOption_zero_right, (mul_assoc_equiv ..).lt_congr_left,
      ← (mul_congr_right (wpow_add_equiv ..)).lt_congr_left]
    exact mul_wpow_lt_wpow' r (add_right_strictMono (Numeric.leftMove_lt hz))
  · rw [mulOption_zero_left, mul_comm, (mul_assoc_equiv ..).lt_congr_left, mul_comm (ω^ z),
      ← (mul_congr_right (wpow_add_equiv ..)).lt_congr_left]
    exact mul_wpow_lt_wpow' _ (add_left_strictMono (Numeric.leftMove_lt hz))
  · exact mulOption_lt_wpow' hr hs (Numeric.leftMove_lt hz) (Numeric.leftMove_lt hw)
      (wpow_add_equiv ..) (wpow_add_equiv ..) (wpow_add_equiv ..)
  · exact mulOption_lt_wpow hr hs (Numeric.lt_rightMove hz) (Numeric.lt_rightMove hw)
      (wpow_add_equiv ..) (wpow_add_equiv ..) (wpow_add_equiv ..)
  · rw [(mul_congr_right (wpow_add_equiv ..)).lt_congr_right, ← (mul_assoc_equiv ..).lt_congr_right,
      Numeric.mul_lt_mul_right (wpow_pos _)]
    exact wpow_lt_mul_wpow' hr (Numeric.lt_rightMove hz)
  · rw [(mul_congr_right (wpow_add_equiv ..)).lt_congr_right, mul_comm (r : IGame),
      (mul_assoc_equiv ..).lt_congr_right, Numeric.mul_lt_mul_left (wpow_pos _), mul_comm]
    exact wpow_lt_mul_wpow' hr (Numeric.lt_rightMove hz)
termination_by (x, y)
decreasing_by igame_wf

theorem wpow_neg_equiv (x : IGame) [Numeric x] : ω^ -x ≈ (ω^ x)⁻¹ := by
  apply equiv_inv_of_mul_eq_one ((wpow_add_equiv ..).symm.trans _)
  rw [← wpow_zero]
  exact wpow_congr (neg_add_equiv x)

theorem wpow_sub_equiv (x y : IGame) [Numeric x] [Numeric y] : ω^ (x - y) ≈ ω^ x / ω^ y :=
  (wpow_add_equiv ..).trans (mul_congr_right (wpow_neg_equiv _))

end Numeric
end IGame

namespace Surreal
open IGame

instance : Wpow Surreal where
  wpow := Quotient.lift (fun x ↦ mk (ω^ x)) fun _ _ h ↦ mk_eq (Numeric.wpow_congr h)

@[simp]
theorem mk_wpow (x : IGame) [Numeric x] : mk (ω^ x) = ω^ (mk x) :=
  rfl

theorem strictMono_wpow : StrictMono (ω^ · : Surreal → _) := by
  rintro ⟨x, _⟩ ⟨y, _⟩
  exact Numeric.wpow_lt_wpow.2

@[simp]
theorem wpow_lt_wpow {x y : Surreal} : ω^ x < ω^ y ↔ x < y :=
  strictMono_wpow.lt_iff_lt

@[simp]
theorem wpow_le_wpow {x y : Surreal} : ω^ x ≤ ω^ y ↔ x ≤ y :=
  strictMono_wpow.le_iff_le

@[simp]
theorem wpow_inj {x y : Surreal} : ω^ x = ω^ y ↔ x = y :=
  strictMono_wpow.injective.eq_iff

@[simp]
theorem wpow_add : ∀ x y : Surreal, ω^ (x + y) = ω^ x * ω^ y := by
  rintro ⟨x, _⟩ ⟨y, _⟩
  exact Surreal.mk_eq (Numeric.wpow_add_equiv x y)

@[simp]
theorem wpow_neg : ∀ x : Surreal, ω^ -x = (ω^ x)⁻¹ := by
  rintro ⟨x, _⟩
  exact Surreal.mk_eq (Numeric.wpow_neg_equiv x)

@[simp]
theorem wpow_sub : ∀ x y : Surreal, ω^ (x - y) = ω^ x / ω^ y := by
  rintro ⟨x, _⟩ ⟨y, _⟩
  exact Surreal.mk_eq (Numeric.wpow_sub_equiv x y)

end Surreal
end
