/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.Mathlib.Archimedean
import CombinatorialGames.Surreal.Real

/-!
# Surreal exponentiation

We define here the ω-map on games and on surreal numbers, representing exponentials with base `ω`.

Among other things, we prove that every non-zero surreal number is commensurate to some unique
`ω^ x`. We express this using `ArchimedeanClass`. There's two important things to note:

- The definition of `ArchimedeanClass` involves absolute values, such that e.g.
  `-ω` is commensurate to `ω`.
- The order in `ArchimedeanClass` is defined so that the equivalence class of `0` is the **largest**
  equivalence class, rather than the smallest.

## Todo

- Prove that `ω^ x` matches ordinal exponentiation for ordinal `x`.
- Define the normal form of a surreal number.
-/

universe u

open Set

/-! ## For Mathlib-/

-- TODO: upstream
theorem Set.image2_eq_range {α β γ : Type*} (f : α → β → γ) (s : Set α) (t : Set β) :
    Set.image2 f s t = Set.range (fun x : s × t ↦ f x.1 x.2) := by
  aesop

namespace ArchimedeanClass

-- TODO: generalize, upstream.
theorem mk_le_mk_of_pos {x y : Surreal} (h : 0 < y) :
    mk x ≤ mk y ↔ ∃ q : ℚ, 0 < q ∧ q * |y| ≤ |x| := by
  constructor
  · rintro ⟨n, hn⟩
    obtain rfl | hn₀ := n.eq_zero_or_pos
    · simp_all
    · use (n : ℚ)⁻¹
      aesop (add simp [inv_mul_le_iff₀])
  · rintro ⟨q, hq₀, hq⟩
    obtain ⟨n, hn⟩ := exists_nat_gt q⁻¹
    use n
    simp only [ArchimedeanOrder.val_of, nsmul_eq_mul]
    rw [← le_inv_mul_iff₀ (mod_cast hq₀)] at hq
    exact hq.trans (mul_le_mul_of_nonneg_right (mod_cast hn.le) (abs_nonneg x))

--  TODO: golf using the previous theorem somehow?
/-- A version of `ArchimedeanClass.mk_le_mk_of_pos` with dyadic rationals. -/
theorem mk_le_mk_of_pos' {x y : Surreal} (h : 0 < y) :
    mk x ≤ mk y ↔ ∃ q : Dyadic, 0 < q ∧ q * |y| ≤ |x| := by
  constructor
  · rintro ⟨n, hn⟩
    obtain rfl | hn₀ := n.eq_zero_or_pos
    · simp_all
    · have hn' : 0 < (n : ℚ)⁻¹ := by simpa
      obtain ⟨q, hq, hq'⟩ := exists_dyadic_btwn hn'
      use q, hq
      simp_rw [ArchimedeanOrder.val_of, nsmul_eq_mul] at hn
      rw [← inv_mul_le_iff₀ (mod_cast hn₀)] at hn
      apply (mul_le_mul_of_nonneg_right _ (abs_nonneg y)).trans hn
      rw [← Rat.cast_lt (K := Surreal)] at hq'
      simpa using hq'.le
  · rintro ⟨q, hq₀, hq⟩
    obtain ⟨n, hn⟩ := exists_nat_gt (q : ℚ)⁻¹
    use n
    simp only [ArchimedeanOrder.val_of, nsmul_eq_mul]
    rw [← le_inv_mul_iff₀ (mod_cast hq₀)] at hq
    exact hq.trans (mul_le_mul_of_nonneg_right (mod_cast hn.le) (abs_nonneg x))

-- TODO: is there any reasonable way to generalize this?
@[simp]
theorem mk_realCast {r : ℝ} (h : r ≠ 0) : mk (r : Surreal) = 0 := by
  apply le_antisymm
  · obtain ⟨n, hn⟩ := exists_nat_gt |r|⁻¹
    use n
    simpa using Real.toSurreal_le_iff.2 <| ((inv_lt_iff_one_lt_mul₀ (abs_pos.2 h)).1 hn).le
  · obtain ⟨n, hn⟩ := exists_nat_gt |r|
    use n
    simpa using Real.toSurreal_le_iff.2 hn.le

-- TODO: generalize, upstream.
@[simp]
theorem mk_ratCast {q : ℚ} (h : q ≠ 0) : mk (q : Surreal) = 0 := by
  rw [← Real.toSurreal_ratCast]
  exact ArchimedeanClass.mk_realCast (mod_cast h)

end ArchimedeanClass

/-! ### ω-map on `IGame` -/

/-- A typeclass for the the `ω^` notation. -/
class Wpow (α : Type*) where
  /-- The ω-map on games. -/
  wpow : α → α

@[inherit_doc] prefix:75 "ω^ " => Wpow.wpow
noncomputable section
namespace IGame

/-- The ω-map on games, which is defined so that `ω^ {s | t}ᴵ = {0, r * ω^ a | r * ω^ b}` for
`a ∈ s`, `b ∈ t`, and `r` ranging over positive dyadic rationals.

The standard definition in the literature instead has `r` ranging over positive reals,
but this makes no difference as to the equivalence class of the games. -/
private def wpow (x : IGame.{u}) : IGame.{u} :=
  {insert 0 (range (fun y : Ioi (0 : Dyadic) × x.leftMoves ↦ y.1 * wpow y.2)) |
    range (fun y : Ioi (0 : Dyadic) × x.rightMoves ↦ y.1 * wpow y.2)}ᴵ
termination_by x
decreasing_by igame_wf

instance : Wpow IGame where
  wpow := wpow

theorem wpow_def (x : IGame.{u}) : ω^ x =
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
    use r, hr, y

theorem mul_wpow_mem_rightMoves_wpow {x y : IGame} {r : Dyadic} (hr : 0 < r)
    (hy : y ∈ x.rightMoves) : r * ω^ y ∈ rightMoves (ω^ x) := by
  rw [rightMoves_wpow]
  use r, hr, y

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
    exact Real.toIGame_le_zero.mpr hr
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
    repeat rw [Numeric.not_lt]
    exact wpow_strictMono_aux.2
  · simpa using mul_wpow_lt_wpow' 1

@[simp]
theorem wpow_le_wpow : ω^ x ≤ ω^ y ↔ x ≤ y := by
  rw [← Numeric.not_lt, wpow_lt_wpow, Numeric.not_lt]

theorem wpow_congr (h : x ≈ y) : ω^ x ≈ ω^ y := by
  simpa [AntisymmRel] using h

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

/-! ### ω-pow on `Surreal` -/

namespace Surreal
open IGame

variable {x y : Surreal}

instance : Wpow Surreal where
  wpow := Quotient.lift (fun x ↦ mk (ω^ x)) fun _ _ h ↦ mk_eq (Numeric.wpow_congr h)

@[simp]
theorem mk_wpow (x : IGame) [Numeric x] : mk (ω^ x) = ω^ (mk x) :=
  rfl

@[simp]
theorem wpow_zero : ω^ (0 : Surreal) = 1 :=
  mk_eq IGame.wpow_zero.antisymmRel

@[simp]
theorem wpow_pos : ∀ x : Surreal, 0 < ω^ x := by
  rintro ⟨x, _⟩
  exact Numeric.wpow_pos x

@[simp]
theorem wpow_ne_zero (x : Surreal) : ω^ x ≠ 0 :=
  (wpow_pos x).ne'

@[simp]
theorem wpow_abs (x : Surreal) : |ω^ x| = ω^ x :=
  abs_of_pos (wpow_pos x)

theorem strictMono_wpow : StrictMono (ω^ · : Surreal → _) := by
  rintro ⟨x, _⟩ ⟨y, _⟩
  exact Numeric.wpow_lt_wpow.2

@[simp]
theorem wpow_lt_wpow : ω^ x < ω^ y ↔ x < y :=
  strictMono_wpow.lt_iff_lt

@[simp]
theorem wpow_le_wpow : ω^ x ≤ ω^ y ↔ x ≤ y :=
  strictMono_wpow.le_iff_le

@[simp]
theorem wpow_inj : ω^ x = ω^ y ↔ x = y :=
  strictMono_wpow.injective.eq_iff

@[simp]
theorem wpow_add : ∀ x y : Surreal, ω^ (x + y) = ω^ x * ω^ y := by
  rintro ⟨x, _⟩ ⟨y, _⟩
  exact mk_eq (Numeric.wpow_add_equiv x y)

@[simp]
theorem wpow_neg : ∀ x : Surreal, ω^ -x = (ω^ x)⁻¹ := by
  rintro ⟨x, _⟩
  exact mk_eq (Numeric.wpow_neg_equiv x)

@[simp]
theorem wpow_sub : ∀ x y : Surreal, ω^ (x - y) = ω^ x / ω^ y := by
  rintro ⟨x, _⟩ ⟨y, _⟩
  exact mk_eq (Numeric.wpow_sub_equiv x y)

theorem mul_wpow_lt_wpow (r : ℝ) (h : x < y) : r * ω^ x < ω^ y := by
  cases x; cases y; exact IGame.Numeric.mul_wpow_lt_wpow r h

theorem wpow_lt_mul_wpow {r : ℝ} (hr : 0 < r) (h : x < y) : ω^ x < r * ω^ y := by
  cases x; cases y; exact IGame.Numeric.wpow_lt_mul_wpow hr h

theorem mul_wpow_lt_mul_wpow (r : ℝ) {s : ℝ} (hs : 0 < s) (h : x < y) : r * ω^ x < s * ω^ y := by
  cases x; cases y; exact IGame.Numeric.mul_wpow_lt_mul_wpow r hs h

/-! ### Archimedean classes -/

-- TODO: How do we write `ArchimedeanClass.mk` in theorem names? `mk` is ambiguous and
-- `archimedeanClassMk` is far too long. Should we introduce notation? What should that look like?

theorem mk_wpow_strictAnti :
    StrictAnti fun x : Surreal ↦ ArchimedeanClass.mk (ω^ x) := by
  refine fun x y h ↦ (ArchimedeanClass.mk_antitoneOn _ (wpow_pos _).le (wpow_pos _).le
    (wpow_le_wpow.2 h.le)).lt_of_not_ge fun ⟨n, hn⟩ ↦ hn.not_gt ?_
  simpa using mul_wpow_lt_wpow n h

@[simp]
theorem mk_wpow_lt_mk_wpow_iff : ArchimedeanClass.mk (ω^ x) < ArchimedeanClass.mk (ω^ y) ↔ y < x :=
  mk_wpow_strictAnti.lt_iff_lt

@[simp]
theorem mk_wpow_le_mk_wpow_iff : ArchimedeanClass.mk (ω^ x) ≤ ArchimedeanClass.mk (ω^ y) ↔ y ≤ x :=
  mk_wpow_strictAnti.le_iff_le

/-- `ω^ x` and `ω^ y` are commensurate iff `x = y`. -/
@[simp]
theorem mk_wpow_inj : ArchimedeanClass.mk (ω^ x) = ArchimedeanClass.mk (ω^ y) ↔ x = y :=
  mk_wpow_strictAnti.injective.eq_iff

private theorem numeric_of_forall_mk_ne_mk {x : IGame} [Numeric x] (h : 0 < x)
    {f : (x.leftMoves ∩ Ioi 0 :) → Subtype Numeric} {g : x.rightMoves → Subtype Numeric}
    (Hf : ∀ y, ω^ (f y).1 ≈ y.1) (Hg : ∀ y, ω^ (g y).1 ≈ y.1) :
    Numeric {range (Subtype.val ∘ f) | range (Subtype.val ∘ g)}ᴵ := by
  sorry

private theorem eq_wpow_of_forall_mk_ne_mk {x : IGame.{u}} [Numeric x] (h : 0 < x)
    {f : (x.leftMoves ∩ Ioi 0 :) → Subtype Numeric.{u}} {g : x.rightMoves → Subtype Numeric.{u}}
    (Hf : ∀ y, ω^ (f y).1 ≈ y.1) (Hg : ∀ y, ω^ (g y).1 ≈ y.1) :
    ω^ x ≈ {range (Subtype.val ∘ f) | range (Subtype.val ∘ g)}ᴵ := by
  sorry

private theorem exists_mk_wpow_eq' {x : IGame.{u}} [Numeric x] (h : 0 < x) :
    ∃ y : Subtype Numeric, ArchimedeanClass.mk (ω^ mk y) = .mk (mk x) := by
  have IHl (y : (x.leftMoves ∩ Ioi 0 :)) :
      have := Numeric.of_mem_leftMoves y.2.1
      ∃ z : Subtype Numeric, ArchimedeanClass.mk (ω^ mk z) = .mk (mk y) := by
    generalize_proofs
    obtain ⟨_, _, hy⟩ := y
    exact exists_mk_wpow_eq' hy
  have IHr (y : x.rightMoves) :
      have := Numeric.of_mem_rightMoves y.2
      ∃ z : Subtype Numeric, ArchimedeanClass.mk (ω^ mk z) = .mk (mk y) := by
    generalize_proofs
    exact exists_mk_wpow_eq' (h.trans (Numeric.lt_rightMove y.2))
  choose f hf using IHl
  choose g hg using IHr
  by_contra! H
  have Ha (a : (x.leftMoves ∩ Ioi 0 :)) :
      have := Numeric.of_mem_leftMoves a.2.1; ArchimedeanClass.mk (mk x) < .mk (mk a) :=
    (ArchimedeanClass.mk_antitoneOn _ a.2.2.le h.le (Numeric.leftMove_lt a.2.1).le).lt_of_ne
      (hf .. ▸ (H _).symm)
  have Hb (b : x.rightMoves) :
      have := Numeric.of_mem_rightMoves b.2; .mk (mk b) < ArchimedeanClass.mk (mk x) :=
    have hb := (Numeric.lt_rightMove b.2).le
    (ArchimedeanClass.mk_antitoneOn _ h.le (h.le.trans hb) hb).lt_of_ne (hg .. ▸ H _)
  have : Numeric {range (Subtype.val ∘ f) | range (Subtype.val ∘ g)}ᴵ := by
    apply Numeric.mk'
    · simp_rw [leftMoves_ofSets, rightMoves_ofSets]
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      simp_rw [Function.comp_apply, ← mk_lt_mk, ← mk_wpow_lt_mk_wpow_iff, hf, hg]
      exact (Hb _).trans (Ha _)
    all_goals aesop (add simp [Subtype.prop])
  apply H ⟨_, this⟩
  congr
  simp_rw [← mk_wpow, mk_eq_mk]
  -- TODO: you actually need to prove the other direction
  -- rw [equiv_comm]
  apply Fits.equiv_of_forall_not_fits
  · constructor <;> intro y hy
    · have := Numeric.of_mem_leftMoves hy
      obtain hy₀ | hy₀ := Numeric.le_or_gt y 0
      · exact (hy₀.trans_lt (IGame.Numeric.wpow_pos _)).not_ge
      · let y' : (x.leftMoves ∩ Ioi 0 :) := ⟨y, hy, hy₀⟩
        obtain ⟨n, hn⟩ := ArchimedeanClass.mk_le_mk.1 (hf y').le
        rw [abs_of_pos hy₀] at hn
        apply (lt_of_le_of_lt (b := n * ω^ (f y').1) ..).not_ge
        · simpa [← mk_le_mk] using hn
        · apply Numeric.leftMove_lt (natCast_mul_wpow_mem_leftMoves_wpow n _)
          simp
    · have := Numeric.of_mem_rightMoves hy
      let y' : x.rightMoves := ⟨y, hy⟩
      obtain ⟨q, hq₀, hq⟩ := (ArchimedeanClass.mk_le_mk_of_pos' (wpow_pos _)).1 (hg y').ge
      rw [abs_of_pos (a := mk _) (h.trans (Numeric.lt_rightMove hy))] at hq
      apply (lt_of_lt_of_le (b := q * ω^ (g y').1) ..).not_ge
      · apply Numeric.lt_rightMove (mul_wpow_mem_rightMoves_wpow hq₀ _)
        simp
      · simpa [← mk_le_mk] using hq
  · rw [forall_leftMoves_wpow, leftMoves_ofSets]
    constructor
    · rw [fits_zero_iff_equiv]
      exact h.not_antisymmRel_symm
    · rintro r hr _ ⟨a, rfl⟩
      dsimp
      rw [not_fits_iff]
      left
      obtain ⟨q, hq₀, hq⟩ := (ArchimedeanClass.mk_le_mk_of_pos' (wpow_pos _)).1 (hf a).ge
      obtain ⟨n, hn⟩ := exists_nat_gt (r * q)
      use a.1, a.2.1
      sorry
  · sorry
termination_by x
decreasing_by igame_wf

/-- Every non-zero surreal is commensurate to some `ω^ x`. -/
theorem exists_mk_wpow_eq (h : x ≠ 0) :
    ∃ y, ArchimedeanClass.mk (ω^ y) = .mk x := by
  obtain h | h := h.lt_or_gt <;> cases x
  · obtain ⟨⟨y, _⟩, hy⟩ := exists_mk_wpow_eq' (IGame.zero_lt_neg.2 h)
    use .mk y
    simpa using hy
  · obtain ⟨⟨y, _⟩, hy⟩ := exists_mk_wpow_eq' h
    exact ⟨_, hy⟩

/-! ### ω-logarithm -/

/-- The ω-logarithm of a positive surreal `x` is the unique surreal `y` such that `x` is
commensurate with `ω^ y`.

As with `Real.log`, we set junk values `wlog 0 = 0` and `wlog (-x) = wlog x`. -/
def wlog (x : Surreal) : Surreal :=
  if h : x = 0 then 0 else Classical.choose (exists_mk_wpow_eq h)

/-- Returns an arbitrary representative for `Surreal.wlog`. -/
def _root_.IGame.wlog (x : IGame) : IGame := by
  classical exact if _ : Numeric x then (Surreal.mk x).wlog.out else 0

instance _root_.IGame.Numeric.wlog (x : IGame) [h : Numeric x] : Numeric x.wlog := by
  rw [IGame.wlog, dif_pos h]
  infer_instance

@[simp]
theorem mk_wlog (x : IGame) [h : Numeric x] : Surreal.mk x.wlog = (Surreal.mk x).wlog := by
  simp_rw [IGame.wlog, dif_pos h, Surreal.out_eq]

@[simp]
theorem wlog_zero : wlog 0 = 0 :=
  dif_pos rfl

@[simp]
theorem mk_wpow_log_eq (h : x ≠ 0) : ArchimedeanClass.mk (ω^ wlog x) = ArchimedeanClass.mk x := by
  rw [wlog, dif_neg h]
  exact Classical.choose_spec (exists_mk_wpow_eq h)

theorem wlog_eq_of_mk_eq_mk (h : ArchimedeanClass.mk (ω^ y) = ArchimedeanClass.mk x) :
    wlog x = y := by
  obtain rfl | hx := eq_or_ne x 0
  · simp at h
  · rwa [← mk_wpow_log_eq hx, eq_comm, mk_wpow_inj] at h

@[simp]
theorem wlog_eq_iff (h : x ≠ 0) :
    wlog x = y ↔ ArchimedeanClass.mk (ω^ y) = ArchimedeanClass.mk x :=
  ⟨fun hy ↦ hy ▸ mk_wpow_log_eq h, wlog_eq_of_mk_eq_mk⟩

theorem wlog_wpow (x : Surreal) : wlog (ω^ x) = x := by
  simp

@[simp]
theorem wlog_neg (x : Surreal) : wlog (-x) = wlog x := by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  · apply wlog_eq_of_mk_eq_mk
    simpa using mk_wpow_log_eq hx

@[simp]
theorem wlog_abs (x : Surreal) : wlog |x| = wlog x :=
  abs_by_cases (wlog · = _) rfl (wlog_neg _)

theorem wlog_surjective : Function.Surjective wlog :=
  fun _ ↦ ⟨_, wlog_wpow _⟩

theorem wlog_monotoneOn : MonotoneOn wlog (Ioi 0) := by
  intro a ha b hb h
  rw [← mk_wpow_le_mk_wpow_iff, mk_wpow_log_eq ha.ne', mk_wpow_log_eq hb.ne']
  apply ArchimedeanClass.mk_antitoneOn _ ha.le hb.le h

theorem wlog_antitoneOn : AntitoneOn wlog (Iio 0) := by
  intro a ha b hb h
  rw [← neg_le_neg_iff] at h
  convert wlog_monotoneOn _ _ h using 1 <;> simp_all

@[simp]
theorem wlog_mul {x y : Surreal} (hx : x ≠ 0) (hy : y ≠ 0) : wlog (x * y) = wlog x + wlog y := by
  apply wlog_eq_of_mk_eq_mk
  rw [wpow_add]
  exact ArchimedeanClass.mk_mul_congr (mk_wpow_log_eq hx) (mk_wpow_log_eq hy)

@[simp]
theorem wlog_realCast (r : ℝ) : wlog r = 0 := by
  obtain rfl | hr := eq_or_ne r 0
  · simp
  · rw [wlog_eq_iff (mod_cast hr), ArchimedeanClass.mk_realCast hr, wpow_zero]

@[simp] theorem wlog_ratCast (q : ℚ) : wlog q = 0 := by simpa using wlog_realCast q
@[simp] theorem wlog_intCast (n : ℤ) : wlog n = 0 := by simpa using wlog_realCast n
@[simp] theorem wlog_natCast (n : ℕ) : wlog n = 0 := by simpa using wlog_realCast n

theorem numeric_of_forall_wlog_ne {x : IGame} [Numeric x] (h : 0 < x)
    (Hf : ∀ y (hy : y ∈ x.leftMoves), 0 < y →
      wlog (@mk y (Numeric.of_mem_leftMoves hy)) ≠ wlog (mk x))
    (Hg : ∀ y (hy : y ∈ x.rightMoves),
      wlog (@mk y (Numeric.of_mem_rightMoves hy)) ≠ wlog (mk x)) :
    Numeric {IGame.wlog '' {y ∈ x.leftMoves | 0 < y} | IGame.wlog '' x.rightMoves}ᴵ := by
  sorry

theorem equiv_wlog_of_forall_wlog_ne {x : IGame} [Numeric x] (h : 0 < x)
    (Hf : ∀ y (hy : y ∈ x.leftMoves), 0 < y →
      wlog (@mk y (Numeric.of_mem_leftMoves hy)) ≠ wlog (mk x))
    (Hg : ∀ y (hy : y ∈ x.rightMoves),
      wlog (@mk y (Numeric.of_mem_rightMoves hy)) ≠ wlog (mk x)) :
    ω^ {IGame.wlog '' {y ∈ x.leftMoves | 0 < y} | IGame.wlog '' x.rightMoves}ᴵ ≈ x := by
  sorry

/-- A game not commensurate with its positive options is a power of `ω`. -/
theorem mem_range_wlog_of_forall_wlog_ne {x : IGame} [Numeric x] (h : 0 < x)
    (Hf : ∀ y (hy : y ∈ x.leftMoves), 0 < y →
      wlog (@mk y (Numeric.of_mem_leftMoves hy)) ≠ wlog (mk x))
    (Hg : ∀ y (hy : y ∈ x.rightMoves),
      wlog (@mk y (Numeric.of_mem_rightMoves hy)) ≠ wlog (mk x)) :
    mk x ∈ range (ω^ ·) := by
  have hn := numeric_of_forall_wlog_ne h Hf Hg
  exact ⟨@mk _ hn, mk_eq (equiv_wlog_of_forall_wlog_ne h Hf Hg)⟩

end Surreal
end
