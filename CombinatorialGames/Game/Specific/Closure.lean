/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Junyan Xu
-/
import CombinatorialGames.Game.GameGraph
import Mathlib.Order.Closure

/-!
# Closure games

We define a very broad class of impartial games we call closure games. These are defined in terms of
a closure operator on `Set α`. A valid move is to insert an element to the set and take the closure.

These games generalize the setup of at least two other important games in combinatorial game theory:
poset games, and Sylver coinage.
-/

variable {α : Type*}

namespace GameGraph

/-- The relation in `ClosureGame`. -/
def ClosureGame.Rel (f : ClosureOperator (Set α)) (t s : f.Closeds) : Prop :=
  ∃ a ∉ s.1, f.toCloseds (insert a s.1) = t

/-- The "closure game" on a closure operator `f` is such that a valid move is to move from a set `s`
to the closure of `insert a s`, where `a ∉ f s`. -/
@[simps!]
def closureGame (f : ClosureOperator (Set α)) : GameGraph f.Closeds where
  moves _ s := {t | ClosureGame.Rel f t s}

namespace ClosureGame
variable {f : ClosureOperator (Set α)} {s t : Set α} {p : Player}

-- TODO: upstream to Mathlib?
theorem mem_of_mem {a : α} (h : a ∈ s) : a ∈ f s := by
  simp_rw [← Set.singleton_subset_iff] at *
  exact h.trans <| f.le_closure _

theorem Rel.irrefl (f : ClosureOperator (Set α)) (s : f.Closeds) : ¬ Rel f s s :=
  fun ⟨a, ha, has⟩ ↦ ha <| has ▸ mem_of_mem (Set.mem_insert a _)

#exit
instance : IsIrrefl _ (Rel f) where
  irrefl := Rel.irrefl f

@[simp]
theorem isOption_eq : (closureGame f).IsOption = Rel f := by
  ext; simp [isOption_iff_mem_union]

open Function in
variable (f) in
theorem subrelation_rel_gt : Subrelation (Rel f) ((· > ·) on f.toCloseds) := by
  intro a b h
  obtain ⟨a, ha, rfl⟩ := h
  refine ⟨f.mono ?_, ?_⟩
  · simp
  · have h' : {a} ⊆ insert a b := by simp
    refine fun h ↦ ha (h <| f.mono h' ?_)
    rw [← Set.singleton_subset_iff]
    exact f.le_closure _

instance (f : ClosureOperator (Set α)) [H : WellFoundedGT f.Closeds] :
    IsWellFounded _ (Rel f) :=
  @Subrelation.isWellFounded _ _ ⟨InvImage.wf _ H.wf⟩ _ (subrelation_rel_gt f)

instance (f : ClosureOperator (Set α)) [WellFoundedGT f.Closeds] :
    IsWellFounded _ (closureGame f).IsOption := by
  rw [isOption_eq]
  infer_instance

theorem toLGame_congr (h : f s = f t) :
    (closureGame f).toLGame s = (closureGame f).toLGame t := by
  sorry
  ext
  simp_rw [moves_toLGame, closureGame_moves, Set.mem_image, Set.mem_setOf_eq]
  congr! 3
  simp [Rel, h]


theorem toIGame_congr [WellFoundedGT f.Closeds] (h : f s = f t) :
    (closureGame f).toIGame s = (closureGame f).toIGame t := by
  apply IGame.toLGame.injective
  simpa using toLGame_congr h

#exit

end ClosureGame
end GameGraph
