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
  x.leftMoves.Finite ∧ x.rightMoves.Finite ∧
    (∀ y ∈ x.leftMoves, ShortAux y) ∧ (∀ y ∈ x.rightMoves, ShortAux y)
termination_by x
decreasing_by igame_wf

/-- A short game is one with finitely many subpositions. That is, the left and right sets are
finite, and all of the games in them are short as well. -/
@[mk_iff short_iff_aux]
class Short (x : IGame) : Prop where
  out : ShortAux x

theorem short_def {x : IGame} : Short x ↔
    x.leftMoves.Finite ∧ x.rightMoves.Finite ∧
      (∀ y ∈ x.leftMoves, Short y) ∧ (∀ y ∈ x.rightMoves, Short y) := by
  simp_rw [short_iff_aux]; rw [ShortAux]

namespace Short
variable {x y : IGame}

theorem mk' (h₁ : x.leftMoves.Finite) (h₂ : x.rightMoves.Finite)
    (h₃ : ∀ y ∈ x.leftMoves, Short y) (h₄ : ∀ y ∈ x.rightMoves, Short y) : Short x :=
  short_def.2 ⟨h₁, h₂, h₃, h₄⟩

theorem finite_leftMoves (x : IGame) [h : Short x] : x.leftMoves.Finite :=
  (short_def.1 h).1

theorem finite_rightMoves (x : IGame) [h : Short x] : x.rightMoves.Finite :=
  (short_def.1 h).2.1

theorem finite_setOf_isOption (x : IGame) [Short x] : {y | IsOption y x}.Finite :=
  (finite_leftMoves x).union (finite_rightMoves x)

instance (x : IGame) [Short x] : Finite x.leftMoves :=
  (Short.finite_leftMoves x).to_subtype

instance (x : IGame) [Short x] : Finite x.rightMoves :=
  (Short.finite_rightMoves x).to_subtype

instance (x : IGame) [Short x] : Finite {y // IsOption y x} :=
  (Short.finite_setOf_isOption x).to_subtype

protected theorem of_mem_leftMoves [h : Short x] (hy : y ∈ x.leftMoves) : Short y :=
  (short_def.1 h).2.2.1 y hy

protected theorem of_mem_rightMoves [h : Short x] (hy : y ∈ x.rightMoves) : Short y :=
  (short_def.1 h).2.2.2 y hy

protected theorem isOption [Short x] (h : IsOption y x) : Short y := by
  cases h with
  | inl h => exact .of_mem_leftMoves h
  | inr h => exact .of_mem_rightMoves h

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
  refine ⟨@finite_setOf_subposition x, fun h ↦ mk' ?_ ?_ ?_ ?_⟩
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
  apply mk'
  · simpa [← Set.image_neg_eq_neg] using (finite_rightMoves x).image _
  · simpa [← Set.image_neg_eq_neg] using (finite_leftMoves x).image _
  · rw [forall_leftMoves_neg]
    intro y hy
    simpa using (Short.of_mem_rightMoves hy).neg
  · rw [forall_rightMoves_neg]
    intro y hy
    simpa using (Short.of_mem_leftMoves hy).neg
termination_by x
decreasing_by igame_wf

@[simp]
theorem neg_iff {x : IGame} : Short (-x) ↔ Short x :=
  ⟨fun _ ↦ by simpa using Short.neg (-x), fun _ ↦ Short.neg x⟩

protected instance add (x y : IGame) [Short x] [Short y] : Short (x + y) := by
  apply mk'
  · simpa using ⟨(finite_leftMoves x).image _, (finite_leftMoves y).image _⟩
  · simpa using ⟨(finite_rightMoves x).image _, (finite_rightMoves y).image _⟩
  · rw [forall_leftMoves_add]
    constructor
    all_goals
      intro z hz
      have := Short.of_mem_leftMoves hz
      exact Short.add ..
  · rw [forall_rightMoves_add]
    constructor
    all_goals
      intro z hz
      have := Short.of_mem_rightMoves hz
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
  apply mk'
  · simpa [Set.image_union] using
      ⟨(finite_leftMoves x).image2 _ (finite_leftMoves y),
        (finite_rightMoves x).image2 _ (finite_rightMoves y)⟩
  · simpa [Set.image_union] using
      ⟨(finite_leftMoves x).image2 _ (finite_rightMoves y),
        (finite_rightMoves x).image2 _ (finite_leftMoves y)⟩
  on_goal 1 => rw [forall_leftMoves_mul]
  on_goal 2 => rw [forall_rightMoves_mul]
  all_goals
  · constructor
    all_goals
      intro a ha b hb
      first | replace ha := Short.of_mem_leftMoves ha | replace ha := Short.of_mem_rightMoves ha
      first | replace hb := Short.of_mem_leftMoves hb | replace hb := Short.of_mem_rightMoves hb
      have := Short.mul a y; have := Short.mul x b; have := Short.mul a b
      rw [mulOption]
      infer_instance
termination_by (x, y)
decreasing_by igame_wf

protected instance mulOption (x y a b : IGame) [Short x] [Short y] [Short a] [Short b] :
    Short (mulOption x y a b) :=
  inferInstanceAs (Short (_ - _))

/-- Undominating a game. This returns garbage values on non-Short games. -/
noncomputable def undominate (x : IGame) : IGame :=
  {{y ∈ {y ∈ x.leftMoves | ∃ (_ : y ∈ x.leftMoves), ∃ z, undominate y = z} |
      ∀ z ∈ x.leftMoves, ¬y < z} |
    {y ∈ {y ∈ x.rightMoves | ∃ (_ : y ∈ x.rightMoves), ∃ z, undominate y = z} |
        ∀ z ∈ x.rightMoves, ¬z < y}}ᴵ
termination_by x
decreasing_by igame_wf

@[simp]
theorem undominate_leftMoves {x : IGame} :
    (undominate x).leftMoves = {y ∈ x.leftMoves | ∀ z ∈ x.leftMoves, ¬y < z} := by
  unfold undominate
  simp

@[simp]
theorem undominate_rightMoves {x : IGame} :
    (undominate x).rightMoves = {y ∈ x.rightMoves | ∀ z ∈ x.rightMoves, ¬z < y} := by
  unfold undominate
  simp

theorem undominate_def {x : IGame} :
    undominate x = {
      {y ∈ x.leftMoves | ∀ z ∈ x.leftMoves, ¬y < z} |
      {y ∈ x.rightMoves | ∀ z ∈ x.rightMoves, ¬z < y}}ᴵ := by
  unfold undominate
  simp

instance {x : IGame} [Short x] : Short (undominate x) := by
  rw [undominate_def, short_def]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · intro y hy
    rw [leftMoves_ofSets] at hy
    exact Short.of_mem_leftMoves hy.1
  · intro y hy
    rw [rightMoves_ofSets] at hy
    exact Short.of_mem_rightMoves hy.1
  all_goals simp [
    Set.setOf_and,
    Set.Finite.inter_of_left (finite_leftMoves x),
    Set.Finite.inter_of_left (finite_rightMoves x),
  ]

theorem exists_ge_in_undominate_of_in_leftMoves {x y : IGame} [Short x] (hy₁ : y ∈ x.leftMoves) :
    ∃ z ∈ (undominate x).leftMoves, y ≤ z := by
  have : Fintype x.leftMoves := Fintype.ofFinite _
  obtain ⟨z, ⟨hyz, hz⟩⟩ := Finset.exists_le_maximal _ (Set.mem_toFinset.mpr hy₁)
  simp_rw [undominate_leftMoves, Set.mem_setOf_eq]
  refine ⟨z, ⟨(Set.mem_toFinset.mp hz.1), fun a ha ↦ ?_⟩, hyz⟩
  exact Maximal.not_gt hz (Set.mem_toFinset.mpr ha)

theorem exists_gt_in_undominate_of_in_rightMoves {x y : IGame} [Short x] (hy₁ : y ∈ x.rightMoves) :
    ∃ z ∈ (undominate x).rightMoves, z ≤ y := by
  sorry

theorem undominate_equiv {x : IGame} [Short x] : x ≈ undominate x := by
  constructor <;> dsimp <;> rw [le_def]
  · rw [undominate_rightMoves]
    exact ⟨fun a ha ↦ .inl (exists_ge_in_undominate_of_in_leftMoves ha),
      fun a ha ↦ .inr ⟨a, ha.1, Preorder.le_refl a⟩⟩
  · rw [undominate_leftMoves]
    refine ⟨fun a ha ↦ .inl ⟨a, ha.1, Preorder.le_refl a⟩,
      fun a ha ↦ .inr (exists_gt_in_undominate_of_in_rightMoves ha)⟩

end Short
end IGame
