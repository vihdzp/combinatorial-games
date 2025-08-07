/-
Copyright (c) 2025 Tristan Figueroa-Reid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristan Figueroa-Reid, Violeta Hernández Palacios
-/
import CombinatorialGames.Game.Computability.FGame
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# The computable bijection between ℕ and FGame

Here, we provide a recursive, computable function derived from Ackermann’s Encoding, and,
while it suffices to show that it's surjective to show its correctness for Plausible,
we aim to prove that it is bijective.

We then construct a `Plausible` instance on `FGame` using this function, allowing us to sample an ℕ
from RNG and use that to construct an `FGame` for counterexamples.

## Todo

- Define plausible (This can be done right now, but `unsafe Repr` is weird. We can make a stable
  `Repr` by sorting over `FGameToNat`.)
- Show that `natToFGame` is bijective using `FGameToNat`.
-/

/- ### For Mathlib -/

instance List.decidableBExU {α : Type*} [DecidableEq α] (p : α → Prop) [DecidablePred p]
    (l : List α) :
    Decidable (∃! x, x ∈ l ∧ p x) :=
  if h : (∃ x, x ∈ l ∧ p x) ∧ ∃ y ∈ l, ∀ x ∈ l, ¬x = y → ¬p x then .isTrue (by
    obtain ⟨⟨x, hx⟩, z, hz⟩ := h
    refine ⟨x, hx, fun y hy ↦ ?_⟩
    exact (not_imp_not.mp (hz.2 y hy.1) hy.2).trans (not_imp_not.mp (hz.2 x hx.1) hx.2).symm)
  else .isFalse (by
    unfold ExistsUnique
    push_neg at h ⊢
    intro x hx
    have ⟨y, hy⟩ := h ⟨x, hx⟩ x hx.1
    exact ⟨y, ⟨hy.1, hy.2.2⟩, hy.2.1⟩)

-- The proof is directly from `Multiset.decidableExistsMultiset`.
-- We don't use the dependent-exists version as the instance as ∃! does not allow multiple binders.
/-- If `p` is a decidable predicate,
so is the unique existence of an element in a multiset satisfying `p`. -/
instance Multiset.decidableExistsUniqueMultiset {α : Type*} [DecidableEq α]
    (p : α → Prop) [DecidablePred p] (m : Multiset α) :
    Decidable (∃! x, x ∈ m ∧ p x) :=
  Quotient.recOnSubsingleton m fun l => decidable_of_iff (∃! a ∈ l, p a) <| by simp

/- ### List indexing constructions -/
-- (do these belong in Mathlib? `List.set'` might.)

/-- Sets many values in a `List` at once through a partial `f`. This will only evaluate `f` up to
`l.length`. -/
def List.set' {α : Type*} (l : List α) (f : ℕ → Option α) : List α :=
  l.mapIdx fun n ↦ (f n).getD

/-- Turns a `s : Finset _` containing tuples of indexes to elements to a list
indexed by said elements, using the inhabited element for any holes.
The return length will include the largest index specified in `s`.

For any values `x ∈ s`, `y ∈ s`, where `x.1 = y.1 → x.2 = y.2`, `x` and `y` will be replaced
with the default value in the resulting `List`. -/
def Finset.asList {α : Type*} [DecidableEq α] [hα : Inhabited α] (s : Finset (ℕ × α)) :
    List α := match (s.image Prod.fst).max with
  | ⊥ => []
  | some n => (List.replicate (n + 1) hα.default).set' fun n ↦ if h : _ then
      some (s.choose (α := (ℕ × α)) (·.1 = n) h).2
    else none

universe u

namespace FGame

/-- The placement enum. This defines where game children go. -/
inductive Placement
| None
| Left
| Right
| Both
deriving DecidableEq, Repr

instance : Inhabited Placement := ⟨.None⟩

/-- Converts a natural number to a placement -/
def Placement.fromNat {n : ℕ} (hn : n < 4) : Placement := match n with
| 0 => None
| 1 => Left
| 2 => Right
| 3 => Both

/-- Converts a placement to a natural number -/
def Placement.toNat : Placement ↪ Nat where
  toFun
  | None => 0
  | Left => 1
  | Right => 2
  | Both => 3
  inj' := fun _ ↦ by aesop

theorem Placement.toNat_lt_four (p : Placement) : p.toNat < 4 := by unfold toNat; aesop

/-- Places a child `FGame` into a parent `FGame` following the `Placement` rule. -/
def Placement.place (parent : FGame) (child : FGame) : Placement → FGame
| None => parent
| Left => {insert child parent.leftMoves | parent.rightMoves}ꟳ
| Right => {parent.leftMoves | insert child parent.rightMoves}ꟳ
| Both => {insert child parent.leftMoves | insert child parent.rightMoves}ꟳ

/-- Take a nat and convert it to an `FGame` by placing the `ofNat n` game at `n` -/
def ofNat (n : ℕ) : SGame :=
  let d := (Nat.digits 4 n).zipIdx
  .mk _ _
    (fun x ↦ ofNat ((d.filter fun x ↦ x.1 = 1 || x.1 = 3)[x.1]).2)
    (fun x ↦ ofNat ((d.filter fun x ↦ x.1 = 2 || x.1 = 3)[x.1]).2)
termination_by n
decreasing_by all_goals
  obtain ⟨hi, -⟩ := List.mem_zipIdx' (List.mem_of_mem_filter (List.getElem_mem x.2))
  apply hi.trans_le
  rw [Nat.digits_length_le_iff (by decide)]
  exact Nat.lt_pow_self (by decide)

/-- An auxiliary definition for defining the inverse of `natToFGame`.
Given a game, we can decompose it into its immediate placements. -/
def toPlacements (g : FGame) : Finset (FGame × Placement) :=
  (g.leftMoves ∪ g.rightMoves).image fun x ↦ (x,
    if x ∈ g.leftMoves then if x ∈ g.rightMoves then Placement.Both else Placement.Left else
      Placement.Right)

theorem toPlacements_mem_isOption {g : FGame} {x} (hx : x ∈ toPlacements g) :
    x.1.IsOption g := by
  simp_rw [toPlacements, Finset.mem_image, Finset.mem_union] at hx
  obtain ⟨_, hy, rfl⟩ := hx
  exact hy

/-- The inverse of `ofNat`. -/
def toNat (g : FGame) : ℕ :=
  Nat.ofDigits 4 (((toPlacements g).attach.image
    fun ⟨x, _⟩ ↦ (toNat x.1, x.2)).asList.map Placement.toNat)
termination_by g
decreasing_by exact .single (toPlacements_mem_isOption (by assumption))

proof_wanted ofNat_rightInverse : Function.RightInverse toNat (FGame.mk ∘ ofNat)
proof_wanted ofNat_leftInverse : Function.LeftInverse toNat (FGame.mk ∘ ofNat)

end FGame
