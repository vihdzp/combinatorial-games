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

theorem zero_mem_leftMoves_opow (x : IGame) : 0 ∈ leftMoves (ω^ x) := by
  simp [leftMoves_opow]

theorem mem_leftMoves_opow {x y : IGame} {r : Dyadic} (hy : y ∈ x.leftMoves) (hr : 0 < r) :
    r * ω^ y ∈ leftMoves (ω^ x) := by
  rw [leftMoves_opow]
  apply mem_insert_of_mem
  use r, hr, y, hy

theorem mem_rightMoves_opow {x y : IGame} {r : Dyadic} (hy : y ∈ x.rightMoves) (hr : 0 < r) :
    r * ω^ y ∈ rightMoves (ω^ x) := by
  rw [rightMoves_opow]
  use r, hr, y, hy

theorem opow_mem_leftMoves_opow {x y : IGame} (hy : y ∈ x.leftMoves) :
    ω^ y ∈ leftMoves (ω^ x) := by
  simpa using mem_leftMoves_opow hy one_pos

theorem opow_mem_rightMoves_opow {x y : IGame} (hy : y ∈ x.rightMoves) :
    ω^ y ∈ rightMoves (ω^ x) := by
  simpa using mem_rightMoves_opow hy one_pos

theorem zero_lf_opow (x : IGame) : 0 ⧏ ω^ x :=
  leftMove_lf (zero_mem_leftMoves_opow x)

@[simp]
theorem opow_zero : ω^ 0 = 1 := by
  ext <;> simp [leftMoves_opow, rightMoves_opow]

private theorem opow_strictMono_aux {x y : IGame} [Numeric x] [Numeric y]
    [Numeric (ω^ x)] [Numeric (ω^ y)] :
    (x < y → ∀ r : ℝ, 0 < r → r * ω^ x < ω^ y) ∧ (x ≤ y → ω^ x ≤ ω^ y) := by
  refine ⟨fun hxy r hr ↦ ?_, fun hxy ↦ ?_⟩
  · obtain (⟨z, hz, hxz⟩ | ⟨z, hz, hzy⟩) := lf_iff_exists_le.1 hxy.not_ge
    · have := Numeric.of_mem_leftMoves hz
      have := Numeric.of_mem_leftMoves (opow_mem_leftMoves_opow hz)
      obtain ⟨n, hn⟩ := exists_nat_gt r
      have : (r : IGame) < (n : IGame) := by simp
      have := mul_lt_mul
      exact (opow_strictMono_aux.2 hxz).trans_lt (Numeric.leftMove_lt hz')
    · have := Numeric.of_mem_rightMoves hz
      have hz' := opow_mem_rightMoves_opow hz
      have := Numeric.of_mem_rightMoves hz'
      exact (Numeric.lt_rightMove hz').trans_le (opow_strictMono_aux.2 hzy)
  · rw [le_iff_forall_lf, forall_leftMoves_opow, forall_rightMoves_opow]
    refine ⟨⟨zero_lf_opow _, fun r hr ↦ ?_⟩, ?_⟩



end IGame
