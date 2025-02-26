/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Violeta Hernández Palacios
-/
import CombinatorialGames.Game.Concrete
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Order.Group.Nat

/-!
# Domineering as a combinatorial game.

We define the game of Domineering, played on a chessboard of arbitrary shape
(possibly even disconnected).
Left moves by placing a domino vertically, while Right moves by placing a domino horizontally.

This is only a fragment of a full development;
in order to successfully analyse positions we would need some more theorems.
Most importantly, we need a general statement that allows us to discard irrelevant moves.
Specifically to domineering, we need the fact that
disjoint parts of the chessboard give sums of games.
-/

namespace PGame

open Function

private theorem pred_fst_ne (m : ℤ × ℤ) : (m.1 - 1, m.2) ≠ m := by aesop
private theorem pred_snd_ne (m : ℤ × ℤ) : (m.1, m.2 - 1) ≠ m := by aesop

/-- A Domineering board is an arbitrary finite subset of `ℤ × ℤ`. -/
def Domineering := Finset (ℤ × ℤ) deriving DecidableEq
@[match_pattern] def toDomineering : Finset (ℤ × ℤ) ≃ Domineering := Equiv.refl _
@[match_pattern] def ofDomineering : Domineering ≃ Finset (ℤ × ℤ) := Equiv.refl _

@[simp] theorem toDomineering_ofDomineering (a : Domineering) :
  toDomineering (ofDomineering a) = a := rfl
@[simp] theorem ofDomineering_toDomineering (s : Finset (ℤ × ℤ)) :
  ofDomineering (toDomineering s) = s := rfl

namespace Domineering

/-- Left can play anywhere that a square and the square below it are open. -/
def left (b : Domineering) : Finset (ℤ × ℤ) :=
  ofDomineering b ∩ (ofDomineering b).map ((Equiv.refl ℤ).prodCongr (Equiv.addRight (1 : ℤ)))

/-- Right can play anywhere that a square and the square to the left are open. -/
def right (b : Domineering) : Finset (ℤ × ℤ) :=
  ofDomineering b ∩ (ofDomineering b).map ((Equiv.addRight (1 : ℤ)).prodCongr (Equiv.refl ℤ))

@[aesop simp]
theorem mem_left {b : Domineering} {m : ℤ × ℤ} :
    m ∈ left b ↔ m ∈ ofDomineering b ∧ (m.1, m.2 - 1) ∈ ofDomineering b :=
  Finset.mem_inter.trans (and_congr Iff.rfl Finset.mem_map_equiv)

@[aesop simp]
theorem mem_right {b : Domineering} {m : ℤ × ℤ} :
    m ∈ right b ↔ m ∈ ofDomineering b ∧ (m.1 - 1, m.2) ∈ ofDomineering b :=
  Finset.mem_inter.trans (and_congr Iff.rfl Finset.mem_map_equiv)

theorem subset_of_mem_left {b : Domineering} {m : ℤ × ℤ} (h : m ∈ left b) :
    {m, (m.1, m.2 - 1)} ⊆ ofDomineering b := fun _ ↦ by
  aesop

theorem subset_of_mem_right {b : Domineering} {m : ℤ × ℤ} (h : m ∈ right b) :
    {m, (m.1 - 1, m.2)} ⊆ ofDomineering b := fun _ ↦ by
  aesop

/-- After Left moves, two vertically adjacent squares are removed from the Domineering. -/
def moveLeft (b : Domineering) (m : ℤ × ℤ) : Domineering :=
  toDomineering <| ((ofDomineering b).erase m).erase (m.1, m.2 - 1)

/-- After Left moves, two horizontally adjacent squares are removed from the Domineering. -/
def moveRight (b : Domineering) (m : ℤ × ℤ) : Domineering :=
  toDomineering <| ((ofDomineering b).erase m).erase (m.1 - 1, m.2)

theorem moveLeft_subset (b : Domineering) (m : ℤ × ℤ) :
    ofDomineering (b.moveLeft m) ⊆ ofDomineering b :=
  (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
theorem moveRight_subset (b : Domineering) (m : ℤ × ℤ) :
    ofDomineering (b.moveRight m) ⊆ ofDomineering b :=
  (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)

/-- Left can move from `b` to `a` when there exists some `m ∈ left b` with `a = b.moveLeft m`. -/
def relLeft (a b : Domineering) : Prop :=
  ∃ m ∈ left b, a = b.moveLeft m

/-- Right can move from `b` to `a` when there exists some `m ∈ right b` with `a = b.moveRight m`. -/
def relRight (a b : Domineering) : Prop :=
  ∃ m ∈ right b, a = b.moveRight m

@[inherit_doc] local infixl:50 " ≺ₗ " => relLeft
@[inherit_doc] local infixr:50 " ≺ᵣ " => relRight

instance : DecidableRel relLeft := fun _ _ ↦ inferInstanceAs (Decidable (∃ _, _))
instance : DecidableRel relRight := fun _ _ ↦ inferInstanceAs (Decidable (∃ _, _))

theorem card_of_mem_left {b : Domineering} {m : ℤ × ℤ} (h : m ∈ left b) :
    2 ≤ (ofDomineering b).card := by
  apply le_of_eq_of_le _ <| Finset.card_mono (subset_of_mem_left h)
  rw [Finset.card_pair (pred_snd_ne m).symm]

theorem card_of_mem_right {b : Domineering} {m : ℤ × ℤ} (h : m ∈ right b) :
    2 ≤ (ofDomineering b).card := by
  apply le_of_eq_of_le _ <| Finset.card_mono (subset_of_mem_right h)
  rw [Finset.card_pair (pred_fst_ne m).symm]

theorem moveLeft_card {b : Domineering} {m : ℤ × ℤ} (h : m ∈ left b) :
    (ofDomineering (moveLeft b m)).card + 2 = (ofDomineering b).card := by
  have := tsub_add_cancel_of_le (card_of_mem_left h)
  rw [moveLeft]
  aesop

theorem moveRight_card {b : Domineering} {m : ℤ × ℤ} (h : m ∈ right b) :
    (ofDomineering (moveRight b m)).card + 2 = Finset.card b := by
  have := tsub_add_cancel_of_le (card_of_mem_right h)
  rw [moveRight]
  aesop

theorem card_of_relLeft {a b : Domineering} (h : a ≺ₗ b) :
    (ofDomineering a).card + 2 = (ofDomineering b).card := by
  obtain ⟨m, hm, rfl⟩ := h
  exact moveLeft_card hm

theorem card_of_relRight {a b : Domineering} (h : a ≺ᵣ b) :
    (ofDomineering a).card + 2 = (ofDomineering b).card := by
  obtain ⟨m, hm, rfl⟩ := h
  exact moveRight_card hm

theorem subrelation_relLeft :
    Subrelation relLeft (InvImage (· < ·) fun b ↦ (ofDomineering b).card) := by
  intro a b h
  rw [InvImage, ← card_of_relLeft h, lt_add_iff_pos_right]
  exact Nat.succ_pos _

theorem subrelation_relRight :
    Subrelation relRight (InvImage (· < ·) fun b ↦ (ofDomineering b).card) := by
  intro a b h
  rw [InvImage, ← card_of_relRight h, lt_add_iff_pos_right]
  exact Nat.succ_pos _

instance : IsWellFounded _ relLeft := subrelation_relLeft.isWellFounded
instance : IsWellFounded _ relRight := subrelation_relRight.isWellFounded

instance : ConcreteGame Domineering where
  subsequentL := relLeft
  subsequentR := relRight
  isWellFounded_subsequent := by
    apply @Subrelation.isWellFounded (r := InvImage (· < ·) fun b ↦ (ofDomineering b).card)
    rintro a b (h | h)
    · exact subrelation_relLeft h
    · exact subrelation_relRight h

end Domineering
end PGame
