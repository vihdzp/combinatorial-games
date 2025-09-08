/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Violeta Hernández Palacios
-/
import CombinatorialGames.Game.Small
import CombinatorialGames.Game.Special

/-!
# Basic definitions about impartial games

In the literature, an impartial game is defined so that its left and right moves are equal, and
every left or right move is also impartial.

However, a weaker definition suffices to prove most of the results of interest: instead of requiring
`-x = x`, we can require `-x ≈ x`. These "weakly impartial" games are closed under negation,
addition, multiplication, and satisfy the Sprague--Grundy theorem.

As such, this file provides two typeclasses: `Impartial` for the standard notion in the literature,
and `WeaklyImpartial` for games satisfying the weaker `-x ≈ x` condition.

## Implementation notes

For discoverability, we put all theorems about either weakly impartial or impartial games in the
common `Impartial` namespace.
-/

universe u

namespace IGame

/-! ### Weakly impartial games -/

private def WeaklyImpartialAux (x : IGame) : Prop :=
  -x ≈ x ∧ ∀ p, ∀ y ∈ x.moves p, WeaklyImpartialAux y
termination_by x
decreasing_by igame_wf

/-- A weakly impartial game is one that's **equivalent** to its negative, such that each left and
right move is also weakly impartial.

This is a sufficient condition for proving the Sprague--Grundy theorem: see
`Impartial.nim_grundy_equiv`.

For the stronger notion of impartiality in the literature, which requires the game to be **equal**
to its negative, see `Impartial`. -/
@[mk_iff weaklyImpartial_iff_aux]
class WeaklyImpartial (x : IGame) : Prop where of_WeaklyImpartialAux ::
  out : WeaklyImpartialAux x

theorem weaklyImpartial_def {x : IGame} :
    x.WeaklyImpartial ↔ -x ≈ x ∧ ∀ p, ∀ y ∈ x.moves p, WeaklyImpartial y := by
  simp_rw [weaklyImpartial_iff_aux]
  rw [WeaklyImpartialAux]

theorem WeaklyImpartial.mk {x : IGame} (h₁ : -x ≈ x)
    (h₂ : ∀ p, ∀ y ∈ x.moves p, WeaklyImpartial y) : WeaklyImpartial x :=
  weaklyImpartial_def.2 ⟨h₁, h₂⟩

@[simp] theorem Impartial.neg_equiv (x : IGame) [hx : WeaklyImpartial x] : -x ≈ x :=
  (weaklyImpartial_def.1 hx).1
@[simp] theorem Impartial.equiv_neg (x : IGame) [hx : WeaklyImpartial x] : x ≈ -x :=
  (Impartial.neg_equiv x).symm

namespace WeaklyImpartial

@[aesop unsafe 50% apply]
protected theorem of_mem_moves {p} {x y : IGame} [h : WeaklyImpartial x] :
    y ∈ x.moves p → WeaklyImpartial y :=
  (weaklyImpartial_def.1 h).2 p y

protected instance zero : WeaklyImpartial 0 := by
  rw [weaklyImpartial_def]; simp

protected instance neg (x : IGame) [WeaklyImpartial x] : WeaklyImpartial (-x) := by
  apply WeaklyImpartial.mk
  · simp
  · simp_rw [moves_neg, Set.mem_neg]
    intro p y hy
    have := WeaklyImpartial.of_mem_moves hy
    rw [← neg_neg y]
    exact .neg _
termination_by x
decreasing_by igame_wf

protected instance add (x y : IGame) [WeaklyImpartial x] [WeaklyImpartial y] :
    WeaklyImpartial (x + y) := by
  apply WeaklyImpartial.mk
  · rw [neg_add]
    exact add_congr (Impartial.neg_equiv x) (Impartial.neg_equiv y)
  · simp_rw [forall_moves_add]
    intro p
    constructor
    all_goals
      intro z hz
      have := WeaklyImpartial.of_mem_moves hz
      exact .add ..
termination_by (x, y)
decreasing_by igame_wf

protected instance sub (x y : IGame) [WeaklyImpartial x] [WeaklyImpartial y] :
    WeaklyImpartial (x - y) :=
  .add x (-y)

/- The product instance is proven in `Game.Impartial.Grundy`. -/

end WeaklyImpartial

namespace Impartial
variable (x y : IGame) [hx : WeaklyImpartial x] [hy : WeaklyImpartial y]

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

theorem add_self_equiv : x + x ≈ 0 :=
  Game.mk_eq_mk.1 (mk_add_self x)

theorem le_comm {x y} [WeaklyImpartial x] [WeaklyImpartial y] : x ≤ y ↔ y ≤ x := by
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

variable {x y}

/-- This lemma doesn't require `x` to be impartial. -/
theorem equiv_iff_add_equiv_zero {x : IGame} : x ≈ y ↔ x + y ≈ 0 := by
  rw [← Game.mk_eq_mk, ← Game.mk_eq_mk, Game.mk_add, Game.mk_zero, add_eq_zero_iff_eq_neg, neg_mk]

/-- This lemma doesn't require `y` to be impartial. -/
theorem equiv_iff_add_equiv_zero' {y : IGame} : x ≈ y ↔ x + y ≈ 0 := by
  rw [antisymmRel_comm, add_comm, equiv_iff_add_equiv_zero]

@[simp]
theorem not_equiv_iff : ¬ x ≈ y ↔ x ‖ y :=
   ⟨(equiv_or_fuzzy x y).resolve_left, IncompRel.not_antisymmRel⟩

@[simp]
theorem not_fuzzy_iff : ¬ x ‖ y ↔ x ≈ y :=
  not_iff_comm.1 not_equiv_iff

theorem fuzzy_iff_add_fuzzy_zero : x ‖ y ↔ x + y ‖ 0 := by
  simpa using (@equiv_iff_add_equiv_zero y _ x).not

@[simp]
theorem le_iff_equiv : x ≤ y ↔ x ≈ y :=
  ⟨fun h ↦ ⟨h, le_comm.1 h⟩, And.left⟩

theorem ge_iff_equiv : y ≤ x ↔ x ≈ y :=
  ⟨fun h ↦ ⟨le_comm.2 h, h⟩, And.right⟩

theorem lf_iff_fuzzy : x ⧏ y ↔ x ‖ y := by simp [comm]
theorem gf_iff_fuzzy : y ⧏ x ↔ x ‖ y := by simp

theorem fuzzy_of_mem_moves {y : IGame} {p : Player} (hy : y ∈ x.moves p) : y ‖ x := by
  have := hx.of_mem_moves hy
  induction p with
  | left => symm; simpa using leftMove_lf hy
  | right => simpa using lf_rightMove hy

private theorem equiv_iff_forall_fuzzy' :
    x ≈ y ↔ (∀ z ∈ xᴸ, z ‖ y) ∧ (∀ z ∈ yᴿ, x ‖ z) := by
  rw [← le_iff_equiv, le_iff_forall_lf]
  congr! with z hz z hz
  all_goals have := WeaklyImpartial.of_mem_moves hz; simp [incompRel_comm]

theorem equiv_iff_forall_fuzzy (p : Player) :
    x ≈ y ↔ (∀ z ∈ x.moves p, z ‖ y) ∧ (∀ z ∈ y.moves (-p), x ‖ z) := by
  induction p with
  | left => exact equiv_iff_forall_fuzzy'
  | right =>
    rw [antisymmRel_comm, equiv_iff_forall_fuzzy', and_comm]
    simp_rw [incompRel_comm]
    rfl

theorem fuzzy_iff_exists_equiv (p : Player) :
    x ‖ y ↔ (∃ z ∈ x.moves p, z ≈ y) ∨ (∃ z ∈ y.moves (-p), x ≈ z) := by
  rw [← not_equiv_iff, equiv_iff_forall_fuzzy p, not_and_or]
  simp_rw [not_forall, ← exists_prop]
  congr! 5 with _ h _ h
  all_goals have := WeaklyImpartial.of_mem_moves h; exact not_fuzzy_iff

theorem equiv_zero (p : Player) : x ≈ 0 ↔ ∀ y ∈ x.moves p, y ‖ 0 := by
  rw [equiv_iff_forall_fuzzy p]; simp

theorem fuzzy_zero (p : Player) : x ‖ 0 ↔ ∃ y ∈ x.moves p, y ≈ 0 := by
  rw [fuzzy_iff_exists_equiv p]; simp

/-- A **strategy stealing** argument. If there's a move in `x`, such that any immediate move could
have also been reached in the first turn, then `x` is won by the first player. -/
theorem fuzzy_zero_of_forall_exists {p : Player} {y} (hy : y ∈ x.moves p)
    (H : ∀ z ∈ y.moves p, ∃ w ∈ x.moves p, z ≈ w) : x ‖ 0 := by
  apply (equiv_or_fuzzy _ _).resolve_left fun hx ↦ ?_
  have := WeaklyImpartial.of_mem_moves hy
  rw [equiv_zero] at hx
  obtain ⟨z, hz, hz'⟩ := (fuzzy_zero _).1 (hx y hy)
  obtain ⟨w, hw, hw'⟩ := H z hz
  exact (hx w hw).not_antisymmRel (hw'.symm.trans hz')

end Impartial

/-! ### Impartial games -/

private def ImpartialAux (x : IGame) : Prop :=
  xᴸ = xᴿ ∧ ∀ p, ∀ i ∈ x.moves p, ImpartialAux i
termination_by x
decreasing_by igame_wf

/-- An impartial game is one that's **equal** to its negative, such that each left and right move is
also impartial.

For a weaker notion of impartiality, which only requires the game to be **equivalent** to its
negative, see `Impartial`. -/
@[mk_iff impartial_iff_aux]
class Impartial (x : IGame) : Prop where of_ImpartialAux ::
  out : ImpartialAux x

theorem impartial_def {x : IGame} :
    x.Impartial ↔ xᴸ = xᴿ ∧ ∀ p, ∀ y ∈ x.moves p, Impartial y := by
  simp_rw [impartial_iff_aux]
  rw [ImpartialAux]

theorem Impartial.mk {x : IGame} (h₁ : xᴸ = xᴿ)
    (h₂ : ∀ p, ∀ y ∈ x.moves p, Impartial y) : Impartial x :=
  impartial_def.2 ⟨h₁, h₂⟩

namespace Impartial
variable (x y : IGame) [hx : Impartial x] [hy : Impartial y]

@[aesop unsafe 50% apply]
protected theorem of_mem_moves {p} {x y : IGame} [h : Impartial x] : y ∈ x.moves p → Impartial y :=
  (impartial_def.1 h).2 p y

theorem moves_const : ∀ p q, x.moves p = x.moves q :=
  Player.const_of_left_eq_right (impartial_def.1 hx).1

@[simp]
theorem neg_eq (x : IGame) [Impartial x] : -x = x := by
  ext1 p
  rw [← Set.image_id (moves p x), moves_neg, moves_const x (-p) p,
    ← Set.image_neg_eq_neg, Set.image_congr]
  intro y hy
  have := Impartial.of_mem_moves hy
  exact neg_eq y
termination_by x
decreasing_by igame_wf

omit hx in
@[simp]
theorem sub_eq : x - y = x + y := by
  rw [sub_eq_add_neg, neg_eq]

instance toWeaklyImpartial (x : IGame) [Impartial x] : WeaklyImpartial x := by
  rw [weaklyImpartial_def]
  refine ⟨?_, fun p y hy ↦ (Impartial.of_mem_moves hy).toWeaklyImpartial⟩
  rw [neg_eq]
termination_by x
decreasing_by igame_wf

protected instance zero : Impartial 0 := by
  rw [impartial_def]
  simp

protected instance star : Impartial ⋆ := by
  rw [impartial_def]
  simp [Impartial.zero]

protected instance neg (x : IGame) [hx : Impartial x] : Impartial (-x) := by
  rwa [neg_eq]

protected instance add (x y : IGame) [Impartial x] [Impartial y] : Impartial (x + y) := by
  refine Impartial.mk ?_ fun p ↦ ?_
  · simp_rw [moves_add, moves_const _ left right]
  · rw [forall_moves_add]
    constructor
    all_goals
      intro z hz
      have := Impartial.of_mem_moves hz
      exact .add ..
termination_by (x, y)
decreasing_by igame_wf

protected instance sub (x y : IGame) [Impartial x] [Impartial y] : Impartial (x - y) :=
  .add x (-y)

protected instance mul (x y : IGame) [Impartial x] [Impartial y] : Impartial (x * y) := by
  refine Impartial.mk ?_ fun p ↦ ?_
  · simp_rw [moves_mul, Player.neg_left, Player.neg_right, moves_const _ left right]
  · simp_rw [forall_moves_mul, mulOption]
    intro p' a ha b hb
    have := Impartial.of_mem_moves ha
    have := Impartial.of_mem_moves hb
    have := Impartial.mul a y; have := Impartial.mul x b; have := Impartial.mul a b;
    infer_instance
termination_by (x, y)
decreasing_by igame_wf

protected instance dicotic (x : IGame) [Impartial x] : Dicotic x := by
  apply Dicotic.mk
  · rw [moves_const _ left right]
  · intro p y hy
    have := Impartial.of_mem_moves hy
    exact Impartial.dicotic y
termination_by x
decreasing_by igame_wf

end Impartial
end IGame
