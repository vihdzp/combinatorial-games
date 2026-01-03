/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Kim Morrison
-/
import CombinatorialGames.Game.IGame
import CombinatorialGames.Tactic.AddInstances
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

theorem short_def {x : IGame} : Short x ↔ ∀ p, (x.moves p).Finite ∧ ∀ y ∈ x.moves p, Short y := by
  simp_rw [short_iff_aux]; rw [ShortAux]

alias ⟨_, Short.mk⟩ := short_def

namespace Short
variable {x y : IGame}

theorem finite_moves (p : Player) (x : IGame) [h : Short x] : (x.moves p).Finite :=
  (short_def.1 h p).1

instance (p : Player) (x : IGame) [Short x] : Finite (x.moves p) :=
  (Short.finite_moves _ x).to_subtype

protected theorem of_mem_moves [h : Short x] {p} (hy : y ∈ x.moves p) : Short y :=
  (short_def.1 h p).2 y hy

/-- `short` eagerly adds all possible `Short` hypotheses. -/
elab "short" : tactic =>
  addInstances <| .mk [`IGame.Short.of_mem_moves]

protected theorem subposition {x : IGame} [Short x] (h : Subposition y x) : Short y := by
  replace h := h.to_reflTransGen
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => assumption
  | head h _ _ =>
    obtain ⟨p, h⟩ := Set.mem_iUnion.1 h
    exact .of_mem_moves h

theorem finite_setOf_subposition (x : IGame) [Short x] : {y | Subposition y x}.Finite := by
  induction x using IGame.moveRecOn generalizing ‹x.Short› with | ind x ih
  convert Set.finite_iUnion fun p => (finite_moves p x).biUnion fun y hy ↦
    (@ih p y hy (.of_mem_moves hy)).insert y
  ext
  rw [Set.mem_setOf, subposition_iff_exists]
  simp

instance (x : IGame) [Short x] : Finite {y // Subposition y x} :=
  (Short.finite_setOf_subposition x).to_subtype

theorem _root_.IGame.short_iff_finite_setOf_subposition {x : IGame} :
    Short x ↔ {y | Subposition y x}.Finite := by
  refine ⟨@finite_setOf_subposition x, fun h ↦ mk fun p ↦ ⟨?_, ?_⟩⟩
  on_goal 1 => refine h.subset fun y hy ↦ ?_
  on_goal 2 => refine fun y hy ↦ short_iff_finite_setOf_subposition.2 <| h.subset fun z hz ↦ ?_
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
  refine mk fun p ↦ ⟨?_, ?_⟩
  · simpa [← Set.image_neg_eq_neg] using (finite_moves _ x).image _
  · rw [forall_moves_neg]
    intro y hy
    simpa using (Short.of_mem_moves hy).neg
termination_by x
decreasing_by igame_wf

@[simp]
theorem neg_iff {x : IGame} : Short (-x) ↔ Short x :=
  ⟨fun _ ↦ by simpa using Short.neg (-x), fun _ ↦ Short.neg x⟩

protected instance add (x y : IGame) [Short x] [Short y] : Short (x + y) := by
  refine mk fun p ↦ ⟨?_, ?_⟩
  · simpa using ⟨(finite_moves _ x).image _, (finite_moves _ y).image _⟩
  · rw [forall_moves_add]
    constructor
    all_goals intro z hz; short; exact Short.add ..
termination_by (x, y)
decreasing_by igame_wf

protected instance sub (x y : IGame) [Short x] [Short y] : Short (x - y) :=
  .add ..

protected instance natCast : ∀ n : ℕ, Short n
  | 0 => inferInstanceAs (Short 0)
  | n + 1 => have := Short.natCast n; inferInstanceAs (Short (n + 1))

protected instance ofNat (n : ℕ) [n.AtLeastTwo] : Short ofNat(n) :=
  inferInstanceAs (Short n)

protected instance intCast : ∀ n : ℤ, Short n
  | .ofNat n => inferInstanceAs (Short n)
  | .negSucc n => inferInstanceAs (Short (-(n + 1)))

protected instance mul (x y : IGame) [Short x] [Short y] : Short (x * y) := by
  refine mk fun p ↦ ⟨?_, ?_⟩
  · simpa [Set.image_union] using
      ⟨(finite_moves _ x).image2 _ (finite_moves _ y),
        (finite_moves _ x).image2 _ (finite_moves _ y)⟩
  · rw [forall_moves_mul]
    intro p' a ha b hb
    replace ha := Short.of_mem_moves ha
    replace hb := Short.of_mem_moves hb
    have := Short.mul a y; have := Short.mul x b; have := Short.mul a b
    rw [mulOption]
    infer_instance
termination_by (x, y)
decreasing_by igame_wf

protected instance mulOption (x y a b : IGame) [Short x] [Short y] [Short a] [Short b] :
    Short (mulOption x y a b) :=
  .sub ..

end Short
end IGame
