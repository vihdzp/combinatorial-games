/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Kim Morrison
-/
import CombinatorialGames.Game.IGame
import Mathlib.Data.Finite.Prod

/-!
# Short games

A combinatorial game is `Short` if it has only finitely many subpositions. In particular, this means
there is a finite set of moves at every point.

We historically defined `Short x` as data, which we then used to enable some degree of computation
on combinatorial games. This functionality is now implemented through the `game_cmp` tactic instead.
-/

universe u

namespace IGame

def ShortAux (x : IGame) : Prop :=
  ∀ p, (x.moves p).Finite ∧ ∀ y ∈ x.moves p, ShortAux y
termination_by x
decreasing_by igame_wf

/-- A short game is one with finitely many subpositions. That is, the left and right sets are
finite, and all of the games in them are short as well. -/
@[mk_iff short_iff_aux]
class Short (x : IGame) : Prop where of_shortAux ::
  out : ShortAux x

theorem short_def {x : IGame} : Short x ↔
    ∀ p, (x.moves p).Finite ∧ ∀ y ∈ x.moves p, Short y := by
  simp_rw [short_iff_aux]; rw [ShortAux]

theorem short_def' {x : IGame} : Short x ↔
    xᴸ.Finite ∧ xᴿ.Finite ∧ (∀ y ∈ xᴸ, Short y) ∧ (∀ y ∈ xᴿ, Short y) := by
  rw [short_def, Player.forall]
  tauto

namespace Short
variable {x y : IGame}

theorem mk (h₁ : xᴸ.Finite) (h₂ : xᴿ.Finite)
    (h₃ : ∀ y ∈ xᴸ, Short y) (h₄ : ∀ y ∈ xᴿ, Short y) : Short x :=
  short_def'.2 ⟨h₁, h₂, h₃, h₄⟩

theorem finite_moves (p : Player) (x : IGame) [h : Short x] : (x.moves p).Finite :=
  (short_def.1 h p).1

theorem finite_setOf_isOption (x : IGame) [Short x] : {y | IsOption y x}.Finite := by
  simp_rw [isOption_iff_mem_union]
  exact (finite_moves _ x).union (finite_moves _ x)

instance (p : Player) (x : IGame) [Short x] : Finite (x.moves p) :=
  (Short.finite_moves _ x).to_subtype

instance (x : IGame) [Short x] : Finite {y // IsOption y x} :=
  (Short.finite_setOf_isOption x).to_subtype

protected theorem of_mem_moves [h : Short x] {p} (hy : y ∈ x.moves p) : Short y :=
  (short_def.1 h p).2 y hy

protected theorem isOption [Short x] (h : IsOption y x) : Short y := by
  simp_rw [isOption_iff_mem_union] at h
  cases h with
  | inl h => exact .of_mem_moves h
  | inr h => exact .of_mem_moves h

alias _root_.IGame.IsOption.short := Short.isOption

protected theorem subposition {x : IGame} [Short x] (h : Subposition y x) : Short y := by
  cases h with
  | single h => exact h.short
  | tail IH h => have := h.short; exact Short.subposition IH
termination_by x
decreasing_by igame_wf

alias _root_.IGame.IsOption.subposition := Short.subposition

theorem finite_setOf_subposition (x : IGame) [Short x] : {y | Subposition y x}.Finite := by
  have : {y | Subposition y x} = {y | IsOption y x} ∪
      ⋃ y ∈ {y | IsOption y x}, {z | Subposition z y} := by
    ext
    rw [Set.mem_setOf_eq, Subposition, Relation.transGen_iff]
    simp [and_comm]
  rw [this]
  refine (finite_setOf_isOption x).union <| (finite_setOf_isOption x).biUnion fun y hy ↦ ?_
  have := hy.short
  exact finite_setOf_subposition y
termination_by x
decreasing_by igame_wf

instance (x : IGame) [Short x] : Finite {y // Subposition y x} :=
  (Short.finite_setOf_subposition x).to_subtype

theorem _root_.IGame.short_iff_finite_setOf_subposition {x : IGame} :
    Short x ↔ {y | Subposition y x}.Finite := by
  refine ⟨@finite_setOf_subposition x, fun h ↦ mk ?_ ?_ ?_ ?_⟩
  any_goals refine h.subset fun y hy ↦ ?_
  any_goals refine fun y hy ↦ short_iff_finite_setOf_subposition.2 <| h.subset fun z hz ↦ ?_
  all_goals igame_wf
termination_by x
decreasing_by igame_wf

@[simp]
protected instance zero : Short 0 := by
  rw [short_def]; simp

@[simp]
protected instance one : Short 1 := by
  rw [short_def]; simp

protected instance neg (x : IGame) [Short x] : Short (-x) := by
  apply mk
  · simpa [← Set.image_neg_eq_neg] using (finite_moves _ x).image _
  · simpa [← Set.image_neg_eq_neg] using (finite_moves _ x).image _
  · rw [forall_moves_neg]
    intro y hy
    simpa using (Short.of_mem_moves hy).neg
  · rw [forall_moves_neg]
    intro y hy
    simpa using (Short.of_mem_moves hy).neg
termination_by x
decreasing_by igame_wf

@[simp]
theorem neg_iff {x : IGame} : Short (-x) ↔ Short x :=
  ⟨fun _ ↦ by simpa using Short.neg (-x), fun _ ↦ Short.neg x⟩

protected instance add (x y : IGame) [Short x] [Short y] : Short (x + y) := by
  rw [short_def]
  intro p
  constructor
  · simpa using ⟨(finite_moves _ x).image _, (finite_moves _ y).image _⟩
  rw [forall_moves_add]
  constructor
  all_goals
    intro z hz
    have := Short.of_mem_moves hz
    exact Short.add ..
termination_by (x, y)
decreasing_by igame_wf

protected instance sub (x y : IGame) [Short x] [Short y] : Short (x - y) :=
  inferInstanceAs (Short (x + -y))

protected instance natCast : ∀ n : ℕ, Short n
  | 0 => inferInstanceAs (Short 0)
  | n + 1 => have := Short.natCast n; inferInstanceAs (Short (n + 1))

protected instance ofNat (n : ℕ) [n.AtLeastTwo] : Short ofNat(n) :=
  inferInstanceAs (Short n)

protected instance intCast : ∀ n : ℤ, Short n
  | .ofNat n => inferInstanceAs (Short n)
  | .negSucc n => inferInstanceAs (Short (-(n + 1)))

protected instance mul (x y : IGame) [Short x] [Short y] : Short (x * y) := by
  rw [short_def]
  intro p
  constructor
  · simpa [Set.image_union] using
      ⟨(finite_moves _ x).image2 _ (finite_moves _ y),
        (finite_moves _ x).image2 _ (finite_moves _ y)⟩
  rw [forall_moves_mul]
  intro p'
  intro a ha b hb
  replace ha := Short.of_mem_moves ha
  replace hb := Short.of_mem_moves hb
  have := Short.mul a y; have := Short.mul x b; have := Short.mul a b
  rw [mulOption]
  infer_instance
termination_by (x, y)
decreasing_by igame_wf

protected instance mulOption (x y a b : IGame) [Short x] [Short y] [Short a] [Short b] :
    Short (mulOption x y a b) :=
  inferInstanceAs (Short (_ - _))

end Short
end IGame
