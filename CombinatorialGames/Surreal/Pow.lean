/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.Surreal.Dyadic

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

prefix:max "ω^ " => opow

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

theorem zero_lf_opow (x : IGame) : 0 ⧏ ω^ x :=
  leftMove_lf (zero_mem_leftMoves_opow x)

@[simp]
theorem opow_zero : ω^ 0 = 1 := by
  ext <;> simp [leftMoves_opow, rightMoves_opow]

end IGame
