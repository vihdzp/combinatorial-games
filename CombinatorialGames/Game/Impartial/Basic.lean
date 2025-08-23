/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Violeta Hernández Palacios
-/
import CombinatorialGames.Game.Basic
import CombinatorialGames.Game.Special

/-!
# Basic definitions about impartial games

We will define an impartial game, one in which left and right can make exactly the same moves.
Our definition differs slightly by saying that the game is always equivalent to its negative,
no matter what moves are played. This allows for games such as poker-nim to be classified as
impartial.
-/

universe u

namespace IGame

private def ImpartialAux (x : IGame) : Prop :=
  -x ≈ x ∧ ∀ p, ∀ i ∈ moves p x, ImpartialAux i
termination_by x
decreasing_by igame_wf

/-- An impartial game is one that's equivalent to its negative, such that each left and right move
is also impartial.

Note that this is a slightly more general definition than the one that's usually in the literature,
as we don't require `x = -x`. Despite this, the Sprague-Grundy theorem still holds: see
`IGame.equiv_nim_grundyValue`.

In such a game, both players have the same payoffs at any subposition. -/
@[mk_iff impartial_iff_aux]
class Impartial (x : IGame) : Prop where of_ImpartialAux ::
  out : ImpartialAux x

theorem impartial_def {x : IGame} :
    x.Impartial ↔ -x ≈ x ∧ ∀ p, ∀ i ∈ moves p x, Impartial i := by
  simp_rw [impartial_iff_aux]
  rw [ImpartialAux]

theorem impartial_def' {x : IGame} :
    x.Impartial ↔ -x ≈ x ∧ (∀ i ∈ xᴸ, Impartial i) ∧ ∀ j ∈ xᴿ, Impartial j := by
  rw [impartial_def, Player.forall]

namespace Impartial
variable (x y : IGame) [hx : Impartial x] [hy : Impartial y]

theorem mk {x : IGame} (h₁ : -x ≈ x)
    (h₂ : ∀ i ∈ xᴸ, Impartial i) (h₃ : ∀ j ∈ xᴿ, Impartial j) : Impartial x :=
  impartial_def'.2 ⟨h₁, h₂, h₃⟩

@[simp] theorem neg_equiv : -x ≈ x := (impartial_def.1 hx).1
@[simp] theorem equiv_neg : x ≈ -x := (neg_equiv _).symm

omit hx in
theorem sub_equiv : x - y ≈ x + y := add_congr_right (neg_equiv y)

@[simp]
theorem neg_mk : -Game.mk x = Game.mk x :=
  Game.mk_eq (equiv_neg x).symm

@[simp]
theorem sub_mk (x : Game) : x - Game.mk y = x + Game.mk y := by
  rw [sub_eq_add_neg, neg_mk]

@[simp]
theorem mk_add_self : Game.mk x + Game.mk x = 0 := by
  rw [add_eq_zero_iff_neg_eq, neg_mk]

theorem add_self_equiv (x : IGame) [Impartial x] : x + x ≈ 0 :=
  Game.mk_eq_mk.1 (mk_add_self x)

@[aesop unsafe 50% apply]
protected theorem of_mem_moves {p} {x y : IGame} [h : Impartial x] :
    y ∈ moves p x → Impartial y :=
  (impartial_def.1 h).2 p y

protected instance zero : Impartial 0 := by
  rw [impartial_def]
  simp

protected instance star : Impartial ⋆ := by
  rw [impartial_def]
  simp [Impartial.zero]

protected instance neg (x : IGame) [Impartial x] : Impartial (-x) := by
  apply mk
  · simp
  all_goals
  · rw [moves_neg]
    intro y hy
    have := Impartial.of_mem_moves hy
    rw [← neg_neg y]
    exact .neg _
termination_by x
decreasing_by igame_wf

protected instance add (x y : IGame) [Impartial x] [Impartial y] : Impartial (x + y) := by
  apply mk
  · rw [neg_add]
    exact add_congr (neg_equiv x) (neg_equiv y)
  all_goals
  · rw [moves_add]
    rintro _ (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩) <;>
    · try have := Impartial.of_mem_moves hz
      try have := Impartial.of_mem_moves hz
      exact .add ..
termination_by (x, y)
decreasing_by igame_wf

protected instance sub (x y : IGame) [Impartial x] [Impartial y] : Impartial (x - y) :=
  .add x (-y)

/-- The product instance is proven in `Game.Impartial.Grundy`. -/

theorem le_comm {x y} [Impartial x] [Impartial y] : x ≤ y ↔ y ≤ x := by
  rw [← IGame.neg_le_neg_iff, (neg_equiv y).le_congr (neg_equiv x)]

@[simp]
theorem not_lt : ¬x < y := by
  apply (lt_asymm · ?_)
  rwa [← IGame.neg_lt_neg_iff, (neg_equiv x).lt_congr (neg_equiv y)]

/-- By setting `y = 0`, we find that in an impartial game, either the first player always wins, or
the second player always wins. -/
theorem equiv_or_fuzzy : x ≈ y ∨ x ‖ y := by
  obtain (h | h | h | h) := lt_or_antisymmRel_or_gt_or_incompRel x y
  · cases not_lt x y h
  · exact .inl h
  · cases not_lt y x h
  · exact .inr h

/-- This lemma doesn't require `x` to be impartial. -/
theorem equiv_iff_add_equiv_zero {x y : IGame} [Impartial y] : x ≈ y ↔ x + y ≈ 0 := by
  rw [← Game.mk_eq_mk, ← Game.mk_eq_mk, Game.mk_add, Game.mk_zero, add_eq_zero_iff_eq_neg, neg_mk]

/-- This lemma doesn't require `y` to be impartial. -/
theorem equiv_iff_add_equiv_zero' {x y : IGame} [Impartial x] : x ≈ y ↔ x + y ≈ 0 := by
  rw [antisymmRel_comm, add_comm, equiv_iff_add_equiv_zero]

variable {x y}

@[simp]
theorem not_equiv_iff : ¬ x ≈ y ↔ x ‖ y :=
   ⟨(equiv_or_fuzzy x y).resolve_left, IncompRel.not_antisymmRel⟩

@[simp]
theorem not_fuzzy_iff : ¬ x ‖ y ↔ x ≈ y :=
  not_iff_comm.1 not_equiv_iff

theorem fuzzy_iff_add_fuzzy_zero : x ‖ y ↔ x + y ‖ 0 := by
  simpa using (@equiv_iff_add_equiv_zero x y).not

@[simp]
theorem le_iff_equiv : x ≤ y ↔ x ≈ y :=
  ⟨fun h ↦ ⟨h, le_comm.1 h⟩, And.left⟩

theorem ge_iff_equiv : y ≤ x ↔ x ≈ y :=
  ⟨fun h ↦ ⟨le_comm.2 h, h⟩, And.right⟩

theorem lf_iff_fuzzy : x ⧏ y ↔ x ‖ y := by simp [comm]
theorem gf_iff_fuzzy : y ⧏ x ↔ x ‖ y := by simp

theorem fuzzy_left {y : IGame} (hy : y ∈ xᴸ) : x ‖ y := by
  have := hx.of_mem_moves hy
  simpa using left_lf hy

theorem left_fuzzy {y : IGame} (hy : y ∈ xᴸ) : y ‖ x :=
  (fuzzy_left hy).symm

theorem right_fuzzy {y : IGame} (hy : y ∈ xᴿ) : y ‖ x := by
  have := hx.of_mem_moves hy
  simpa using lf_right hy

theorem fuzzy_right {y : IGame} (hy : y ∈ xᴿ) : x ‖ y :=
  (right_fuzzy hy).symm

/-- This version is stated in terms of left moves of `x` and right moves of `y`. -/
theorem equiv_iff_forall_fuzzy :
    x ≈ y ↔ (∀ z ∈ xᴸ, z ‖ y) ∧ (∀ z ∈ yᴿ, x ‖ z) := by
  rw [← le_iff_equiv, le_iff_forall_lf]
  congr! with z hz z hz
  on_goal 1 => replace hz := hx.of_mem_moves hz
  on_goal 2 => replace hz := hy.of_mem_moves hz
  all_goals simp [incompRel_comm]

/-- This version is stated in terms of right moves of `x` and left moves of `y`. -/
theorem equiv_iff_forall_fuzzy' :
    x ≈ y ↔ (∀ z ∈ xᴿ, z ‖ y) ∧ (∀ z ∈ yᴸ, x ‖ z) := by
  rw [antisymmRel_comm, equiv_iff_forall_fuzzy, and_comm]
  simp_rw [incompRel_comm]

/-- This version is stated in terms of left moves of `y` and right moves of `x`. -/
theorem fuzzy_iff_exists_equiv' :
    x ‖ y ↔ (∃ z ∈ yᴸ, x ≈ z) ∨ (∃ z ∈ xᴿ, z ≈ y) := by
  rw [← lf_iff_fuzzy, lf_iff_exists_le]
  congr! 3 with z z <;> rw [and_congr_right_iff] <;> intro hz
  on_goal 1 => replace hz := hy.of_mem_moves hz
  on_goal 2 => replace hz := hx.of_mem_moves hz
  all_goals simp

/-- This version is stated in terms of right moves of `y` and left moves of `x`. -/
theorem fuzzy_iff_exists_equiv :
    x ‖ y ↔ (∃ z ∈ yᴿ, x ≈ z) ∨ (∃ z ∈ xᴸ, z ≈ y) := by
  rw [incompRel_comm, fuzzy_iff_exists_equiv', or_comm]
  simp_rw [antisymmRel_comm]

/-- This version is stated in terms of left moves of `x`. -/
theorem equiv_zero : x ≈ 0 ↔ ∀ y ∈ xᴸ, y ‖ 0 := by
  rw [equiv_iff_forall_fuzzy]; simp

/-- This version is stated in terms of right moves of `x`. -/
theorem equiv_zero' : x ≈ 0 ↔ ∀ y ∈ xᴿ, y ‖ 0 := by
  rw [equiv_iff_forall_fuzzy']; simp

/-- This version is stated in terms of left moves of `x`. -/
theorem fuzzy_zero : x ‖ 0 ↔ ∃ y ∈ xᴸ, y ≈ 0 := by
  rw [fuzzy_iff_exists_equiv]; simp

/-- This version is stated in terms of right moves of `x`. -/
theorem fuzzy_zero' : x ‖ 0 ↔ ∃ y ∈ xᴿ, y ≈ 0 := by
  rw [fuzzy_iff_exists_equiv']; simp

/-- A **strategy stealing** argument. If there's a move in `x`, such that any immediate move could
have also been reached in the first turn, then `x` is won by the first player.

This version of the theorem is stated exclusively in terms of left moves; see
`fuzzy_zero_of_forall_exists_moveRight` for a version stated with right moves. -/
theorem fuzzy_zero_of_forall_exists_moveLeft {y} (hy : y ∈ xᴸ)
    (H : ∀ z ∈ yᴸ, ∃ w ∈ xᴸ, z ≈ w) : x ‖ 0 := by
  apply (equiv_or_fuzzy _ _).resolve_left fun hx ↦ ?_
  have := Impartial.of_mem_moves hy
  rw [equiv_zero] at hx
  obtain ⟨z, hz, hz'⟩ := fuzzy_zero.1 (hx y hy)
  obtain ⟨w, hw, hw'⟩ := H z hz
  exact (hx w hw).not_antisymmRel (hw'.symm.trans hz')

/-- A **strategy stealing** argument. If there's a move in `x`, such that any immediate move could
have also been reached in the first turn, then `x` is won by the first player.

This version of the theorem is stated exclusively in terms of right moves; see
`fuzzy_zero_of_forall_exists_moveLeft` for a version stated with left moves. -/
theorem fuzzy_zero_of_forall_exists_moveRight {y} (hy : y ∈ xᴿ)
    (H : ∀ z ∈ yᴿ, ∃ w ∈ xᴿ, z ≈ w) : x ‖ 0 := by
  rw [← neg_fuzzy_zero]
  apply fuzzy_zero_of_forall_exists_moveLeft (x := -x) (y := -y)
  · simpa
  · simpa only [forall_moves_neg, exists_moves_neg, neg_equiv_neg_iff]

end Impartial
end IGame
