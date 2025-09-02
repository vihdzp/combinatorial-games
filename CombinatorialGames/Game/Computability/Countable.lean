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

/-- Places a child `FGame` into a parent `FGame` following the `Fin 4` rule.
`0` is nothing, `1` is left, `2` is right, `3` is both. This convention follows for the rest
of this file. -/
def place (parent : FGame) (child : FGame) : Fin 4 → FGame
| 0 => parent
| 1 => {insert child parent.leftMoves | parent.rightMoves}ꟳ
| 2 => {parent.leftMoves | insert child parent.rightMoves}ꟳ
| 3 => {insert child parent.leftMoves | insert child parent.rightMoves}ꟳ

private def _root_.SGame.ofNat (n : ℕ) : SGame :=
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

/-- Take a nat and convert it to an `FGame` by placing the `ofNat n` game at `n` -/
def ofNat (n : ℕ) : FGame :=
  .mk (SGame.ofNat n)

theorem mem_moves {x : FGame} {a n : ℕ} (ha : a ≠ 0) :
    (∃ k : Fin _, ofNat ((Nat.digits 4 n).zipIdx.filter (fun x ↦ x.1 = a || x.1 = 3))[k.1].2 = x) ↔
    ∃ m, x = ofNat m ∧ ((Nat.digits 4 n)[m]?.getD 0 ∈ ({a, 3} : Set _)) := by
  constructor
  · rintro ⟨b, rfl⟩
    refine ⟨_, rfl, ?_⟩
    obtain ⟨hl, hl'⟩ := List.mem_zipIdx' (List.mem_of_mem_filter (List.getElem_mem b.2))
    dsimp at hl hl'
    rw [List.getElem?_eq_getElem hl, ← hl']
    simpa using List.getElem_filter b.2
  · rintro ⟨b, rfl, hb⟩
    have : ∃ d, (d, b) ∈ (Nat.digits 4 n).zipIdx.filter (fun x ↦ x.1 = a || x.1 = 3) := by
      aesop (add simp [List.mem_zipIdx_iff_getElem?, Option.getD_eq_iff])
    obtain ⟨d, hd⟩ := this
    obtain ⟨i, hi, hi'⟩ := List.getElem_of_mem hd
    use ⟨i, hi⟩
    rw [hi']

theorem mem_leftMoves_ofNat' {x : FGame} {n : ℕ} :
    x ∈ leftMoves (ofNat n) ↔
    ∃ m, x = ofNat m ∧ (Nat.digits 4 n).getD m 0 ∈ ({1, 3} : Set _) := by
  rw [ofNat, SGame.ofNat]
  simpa using mem_moves one_ne_zero

theorem mem_rightMoves_ofNat' {x : FGame} {n : ℕ} :
    x ∈ rightMoves (ofNat n) ↔
    ∃ m, x = ofNat m ∧ (Nat.digits 4 n).getD m 0 ∈ ({2, 3} : Set _) := by
  rw [ofNat, SGame.ofNat]
  simpa using mem_moves two_ne_zero

/-- An auxiliary definition for defining the inverse of `natToFGame`.
Given a game, we can decompose it into its immediate placements. -/
def toPlacements (g : FGame) : Finset (FGame × Fin 4) :=
  (g.leftMoves ∪ g.rightMoves).image fun x ↦ (x,
    if x ∈ g.leftMoves then if x ∈ g.rightMoves then 3 else 1 else 2)

theorem toPlacements_mem_isOption {g : FGame} {x} (hx : x ∈ toPlacements g) :
    x.1.IsOption g := by
  simp_rw [toPlacements, Finset.mem_image, Finset.mem_union] at hx
  obtain ⟨_, hy, rfl⟩ := hx
  exact hy

/-- The inverse of `ofNat`. -/
def toNat (g : FGame) : ℕ :=
  Nat.ofDigits 4 ((toPlacements g).attach.image fun ⟨x, _⟩ ↦ (toNat x.1, x.2)).asList
termination_by g
decreasing_by exact .single (toPlacements_mem_isOption (by assumption))

theorem toNat_def (g : FGame) :
    toNat g = Nat.ofDigits 4 ((toPlacements g).image fun x ↦ (toNat x.1, x.2)).asList := by
  rw [toNat]
  -- TODO: :(
  show Nat.ofDigits 4 (g.toPlacements.attach.image
    fun x ↦ ((fun x ↦ (x.1.toNat, x.2)) ∘ Subtype.val) x).asList = _
  rw [← Finset.image_image, Finset.attach_image_val]

end FGame
