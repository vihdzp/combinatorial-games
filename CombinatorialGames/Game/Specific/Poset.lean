/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.Game.Concrete
import CombinatorialGames.Game.Impartial.Basic
import Mathlib.Order.WellQuasiOrder

/-!
# Poset games

Let `α` be a partially ordered type (in fact, a preorder suffices). One can define the following
impartial game: two players alternate turns choosing an element `a : α`, and "removing" the entire
interval `Ici a` from the poset. As usual, whoever runs out of moves loses.

In a general poset, this game need not terminate. Adding the condition that `α` is well
quasi-ordered (well-founded with no infinite antichains) is both sufficient and necessary to
guarantee a finite game.

This setup generalizes other well-known games within CGT, most notably Chomp, which is simply the
poset game on `(Fin m × Fin n) \ {⊥}`.

## Main results

* `ConcreteGame.Poset.impartial_toIGame`: poset games are impartial
* `ConcreteGame.Poset.univ_fuzzy_zero`: any poset game with a top element is won by the second
  player, shown via a strategy stealing argument
-/

variable {α : Type*} [Preorder α]

open Set

namespace ConcreteGame.Poset

/-! ### Poset relation -/

/-- A valid move in the poset game is to change set `t` to set `s`, whenever `s = t \ Ici a` for
some `a ∈ t`.

In a WQO, this relation is well-founded. -/
def Rel (s t : Set α) : Prop :=
  ∃ a ∈ t, s = t \ Ici a

@[inherit_doc]
local infixl:50 " ≺ " => Rel

theorem subrelation_rel : @Subrelation (Set α) (· ≺ ·) (· ⊂ ·) := by
  rintro x y ⟨a, ha, rfl⟩
  refine ⟨diff_subset, not_subset.2 ⟨a, ha, ?_⟩⟩
  simp

theorem not_rel_empty (s : Set α) : ¬ s ≺ ∅ := by
  simp [Rel]

theorem rel_irrefl (s : Set α) : ¬ s ≺ s :=
  fun h ↦ ssubset_irrefl s <| subrelation_rel h

instance : IsIrrefl (Set α) (· ≺ ·) where
  irrefl := rel_irrefl

theorem top_compl_rel_univ {α : Type*} [PartialOrder α] [OrderTop α] : {⊤}ᶜ ≺ @univ α := by
  use ⊤
  simp [Ici, compl_eq_univ_diff]

theorem rel_univ_of_rel_top_compl {α : Type*} [PartialOrder α] [OrderTop α] {s : Set α}
    (h : s ≺ {⊤}ᶜ) : s ≺ univ := by
  obtain ⟨a, _, rfl⟩ := h
  use a, mem_univ _
  rw [compl_eq_univ_diff, diff_diff, union_eq_right.2]
  simp

theorem wellFounded_rel [WellQuasiOrderedLE α] : @WellFounded (Set α) (· ≺ ·) := by
  rw [WellFounded.wellFounded_iff_no_descending_seq]
  refine ⟨fun ⟨f, hf⟩ ↦ ?_⟩
  choose g hg using id hf
  obtain ⟨m, n, h, h'⟩ := wellQuasiOrdered_le g
  let f' := @RelEmbedding.natGT _ (· < ·) _ f fun n ↦ subrelation_rel (hf n)
  have : g n ∈ f (m + 1) := by
    obtain rfl | h := h.nat_succ_le.eq_or_lt
    · exact (hg _).1
    · exact (f'.map_rel_iff.2 h).le (hg n).1
  rw [(hg m).2, mem_diff] at this
  exact this.2 h'

instance isWellFounded_rel [WellQuasiOrderedLE α] : IsWellFounded (Set α) (· ≺ ·) :=
  ⟨wellFounded_rel⟩

/-! ### Poset game -/

-- TODO: add stuff on `LGame`

section IGame
variable [WellQuasiOrderedLE α]

variable (α) in
/-- The poset game, played on a poset `α`. -/
abbrev _root_.ConcreteGame.poset : ConcreteGame (Set α) :=
  .ofImpartial fun x ↦ {y | Poset.Rel y x}

instance : IsWellFounded _ (poset α).IsOption := by
  simpa using isWellFounded_rel

/-- A state of the poset game on `α`. -/
noncomputable def toIGame (s : Set α) : IGame :=
  (poset α).toIGame s

@[simp]
theorem leftMoves_toIGame (s : Set α) : (toIGame s).leftMoves = toIGame '' {t | Rel t s} :=
  ConcreteGame.leftMoves_toIGame ..

@[simp]
theorem rightMoves_toIGame (s : Set α) : (toIGame s).rightMoves = toIGame '' {t | Rel t s} :=
  ConcreteGame.rightMoves_toIGame ..

@[simp]
protected theorem neg_toIGame (s : Set α) : -toIGame s = toIGame s :=
  neg_toIGame_ofImpartial _ s

protected instance impartial_toIGame (s : Set α) : (toIGame s).Impartial :=
  impartial_toIGame_ofImpartial _ s

-- TODO: this should generalize to a `Preorder`.
-- A game should be equal to its antisymmetrization.

/-- Any poset game on a toIGame with a top element is won by the first player. This is proven by
a strategy stealing argument with `{⊤}ᶜ`. -/
theorem univ_fuzzy_zero {α : Type*} [PartialOrder α] [WellQuasiOrderedLE α] [OrderTop α] :
    toIGame (@univ α) ‖ 0 := by
  apply IGame.Impartial.fuzzy_zero_of_forall_exists_moveLeft
    (mem_leftMoves_toIGame_of_mem (top_compl_rel_univ))
  refine fun z hz ↦ ⟨z, ?_, by rfl⟩
  rw [ConcreteGame.leftMoves_toIGame, mem_image] at hz ⊢
  exact ⟨_, rel_univ_of_rel_top_compl hz.choose_spec.1, hz.choose_spec.2⟩

end IGame
end ConcreteGame.Poset
