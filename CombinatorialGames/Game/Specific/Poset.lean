/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Order.WellQuasiOrder
import CombinatorialGames.Game.Concrete
import CombinatorialGames.Game.Impartial

/-!
# Poset games

Let `α` be a partially ordered type (in fact, a preorder suffices). One can define the following
impartial game: two players alternate turns choosing an element `a : α`, and "removing" the entire
interval `Ici a` from the poset. As usual, whoever runs out of moves loses.

In a general poset, this game need not terminate. Adding the condition that `α` is well
quasi-ordered (well-founded with no infinite antichains) is both sufficient and necessary to
guarantee a finite game.

This setup generalizes other well-known games within CGT, most notably Chomp, which is simply the
poset game on `(Fin m → Fin n) \ {⊥}`.

## Main results

* `PGame.impartial_posetPos`: poset games are impartial
* `PGame.poset_fuzzy_zero`: any poset game with a top element is won by the second player, shown via
  a strategy stealing argument
-/

variable {α : Type*} [Preorder α]

open Set

section Set

/-- A valid move in the poset game is to change set `t` to set `s`, whenever `s = t \ Ici a` for
some `a ∈ t`.

In a WQO, this relation is well-founded. -/
def posetRel (s t : Set α) : Prop :=
  ∃ a ∈ t, s = t \ Ici a

@[inherit_doc]
local infixl:50 " ≺ " => posetRel

theorem subrelation_posetRel : @Subrelation (Set α) (· ≺ ·) (· ⊂ ·) := by
  rintro x y ⟨a, ha, rfl⟩
  refine ⟨diff_subset, not_subset.2 ⟨a, ha, ?_⟩⟩
  simp

theorem not_posetRel_empty (s : Set α) : ¬ s ≺ ∅ := by
  simp [posetRel]

theorem posetRel_irrefl (s : Set α) : ¬ s ≺ s :=
  fun h ↦ ssubset_irrefl s <| subrelation_posetRel h

instance : IsIrrefl (Set α) (· ≺ ·) where
  irrefl := posetRel_irrefl

theorem top_compl_posetRel_univ {α : Type*} [PartialOrder α] [OrderTop α] : {⊤}ᶜ ≺ @univ α := by
  use ⊤
  simp [Ici, compl_eq_univ_diff]

theorem posetRel_univ_of_posetRel_top_compl {α : Type*} [PartialOrder α] [OrderTop α] {s : Set α}
    (h : s ≺ {⊤}ᶜ) : s ≺ univ := by
  obtain ⟨a, _, rfl⟩ := h
  use a, mem_univ _
  rw [compl_eq_univ_diff, diff_diff, union_eq_right.2]
  simp

theorem wellFounded_posetRel [WellQuasiOrderedLE α] : @WellFounded (Set α) (· ≺ ·) := by
  rw [WellFounded.wellFounded_iff_no_descending_seq]
  refine ⟨fun ⟨f, hf⟩ ↦ ?_⟩
  have hf' := hf -- Is there a way to make `choose` not delete my hypothesis?
  choose g hg using hf
  obtain ⟨m, n, h, h'⟩ := wellQuasiOrdered_le g
  let f' := @RelEmbedding.natGT _ (· < ·) _ f fun n ↦ subrelation_posetRel (hf' n)
  have : g n ∈ f (m + 1) := by
    obtain rfl | h := h.nat_succ_le.eq_or_lt
    · exact (hg _).1
    · exact (f'.map_rel_iff.2 h).le (hg n).1
  rw [(hg m).2, mem_diff] at this
  exact this.2 h'

instance isWellFounded_posetRel [WellQuasiOrderedLE α] : IsWellFounded (Set α) (· ≺ ·) :=
  ⟨wellFounded_posetRel⟩

end Set

namespace PGame
variable [WellQuasiOrderedLE α]

/-- The set of states in a poset game. This is a type alias for `Set α`. -/
def Poset (α : Type*) [Preorder α] [WellQuasiOrderedLE α] := Set α
@[match_pattern] def toPoset : Set α ≃ Poset α := Equiv.refl _
@[match_pattern] def ofPoset : Poset α ≃ Set α := Equiv.refl _

@[simp] theorem toPoset_ofPoset (a : Poset α) : toPoset (ofPoset a) = a := rfl
@[simp] theorem ofPoset_toPoset (a : Set α) : ofPoset (toPoset a) = a := rfl

namespace Poset
open ConcreteGame

/-- A valid move in the poset game is to change set `t` to set `s`, whenever `s = t \ Ici a` for
some `a ∈ t`. -/
def rel (a b : Poset α) : Prop :=
  posetRel (ofPoset a) (ofPoset b)

@[inherit_doc]
local infixl:50 " ≺ " => rel

instance : IsWellFounded (Poset α) rel := isWellFounded_posetRel
instance : WellFoundedRelation (Poset α) := ⟨rel, isWellFounded_posetRel.wf⟩
instance : ConcreteGame (Poset α) := .ofImpartial rel

protected theorem neg_toPGame (a : Poset α) : -toPGame a = toPGame a :=
  neg_toPGame rfl a

instance (a : Poset α) : Impartial (toPGame a) :=
  impartial_toPGame rfl a

-- TODO: this should generalize to a `Preorder`.
-- A game should be equal to its antisymmetrization.

/-- Any poset game on a poset with a top element is won by the first player. This is proven by
a strategy stealing argument with `{⊤}ᶜ`. -/
theorem univ_fuzzy_zero {α : Type*} [PartialOrder α] [WellQuasiOrderedLE α] [OrderTop α] :
    toPGame (toPoset (@univ α)) ‖ 0 := by
  apply Impartial.fuzzy_zero_of_forall_exists_moveLeft _
    (toLeftMovesPGame ⟨_, top_compl_posetRel_univ⟩)
  rw [moveLeft_toPGame_toLeftMovesPGame]
  refine fun i ↦ ⟨toLeftMovesPGame ⟨_, posetRel_univ_of_posetRel_top_compl
    (toLeftMovesPGame_symm_prop i)⟩, ?_⟩
  simp

end Poset
end PGame
