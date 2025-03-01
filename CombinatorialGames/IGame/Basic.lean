/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.IGame.IGame

universe u

noncomputable section

open IGame Set Pointwise

/-- Games up to equivalence.

If `x` and `y` are combinatorial games (`IGame`), we say that `x ≈ y` when both `x ≤ y` and `y ≤ x`.
Broadly, this means neither player has a preference in playing either game, as a component of a
larger game. This is the standard meaning of `x = y` in the literature, though it is not a strict
equality, e.g. `{0, 1 | 0}` and `{1 | 0}` are equivalent, but not identical as the former has an
extra move for Left.

In particular, note that a `Game` has no well-defined notion of left and right options. This means
you should prefer `IGame` when analyzing specific games. -/
def Game : Type (u + 1) :=
  Antisymmetrization IGame (· ≤ ·)

namespace Game

/-- The quotient map from `IGame` into `Game`. -/
def mk (x : IGame) : Game := Quotient.mk _ x
theorem mk_eq_mk {x y : IGame} : mk x = mk y ↔ x ≈ y := Quotient.eq

alias ⟨_, mk_eq⟩ := mk_eq_mk

@[cases_eliminator]
theorem ind {P : Game → Prop} (H : ∀ y, P (mk y)) (x : Game) : P x :=
  Quotient.ind H x

/-- Choose an element of the equivalence class using the axiom of choice. -/
def out (x : Game) : IGame := Quotient.out x
@[simp] theorem out_eq (x : Game) : mk x.out = x := Quotient.out_eq x

theorem mk_out_equiv (x : IGame) : (mk x).out ≈ x := Quotient.mk_out (s := AntisymmRel.setoid ..) x
theorem equiv_mk_out (x : IGame) : x ≈ (mk x).out := (mk_out_equiv x).symm

/-- Construct a `Game` from its left and right sets.

This is given notation `{s | t}ᴳ`, where the superscript `G` is to disambiguate from set builder
notation, and from the analogous constructor on `IGame`.

Note that although this function is well-defined, recovering the left/right sets from a game is not,
as there are many sets that can generate a single game. -/
def ofSets (s t : Set Game.{u}) [Small.{u} s] [Small.{u} t] : Game.{u} :=
  mk {out '' s | out '' t}ᴵ

@[inherit_doc] notation "{" s " | " t "}ᴳ" => ofSets s t

theorem mk_ofSets (s t : Set IGame.{u}) [Small.{u} s] [Small.{u} t] :
    mk {s | t}ᴵ = {mk '' s | mk '' t}ᴳ := by
  refine mk_eq <| IGame.equiv_of_exists ?_ ?_ ?_ ?_ <;>
    simpa using fun a ha ↦ ⟨a, ha, equiv_mk_out a⟩

instance : Zero Game := ⟨mk 0⟩
instance : One Game := ⟨mk 1⟩
instance : Add Game := ⟨Quotient.map₂ _ @add_congr⟩
instance : Neg Game := ⟨Quotient.map _ @neg_congr⟩
instance : PartialOrder Game := inferInstanceAs (PartialOrder (Antisymmetrization ..))
instance : Inhabited Game := ⟨0⟩

instance : OrderedAddCommGroup Game where
  zero_add := by
    rintro ⟨x⟩
    change mk (0 + _) = mk _
    rw [zero_add]
  add_zero := by
    rintro ⟨x⟩
    change mk (_ + 0) = mk _
    rw [add_zero]
  add_comm := by
    rintro ⟨x⟩ ⟨y⟩
    change mk (_ + _) = mk (_ + _)
    rw [add_comm]
  add_assoc := by
    rintro ⟨x⟩ ⟨y⟩ ⟨z⟩
    change mk (_ + _ + _) = mk (_ + (_ + _))
    rw [add_assoc]
  neg_add_cancel := by
    rintro ⟨a⟩
    exact mk_eq (neg_add_equiv _)
  add_le_add_left := by
    rintro ⟨a⟩ ⟨b⟩ h ⟨c⟩
    exact add_le_add_left (α := IGame) h _
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : AddMonoidWithOne Game where

@[simp] theorem mk_zero : mk 0 = 0 := rfl
@[simp] theorem mk_one : mk 1 = 1 := rfl
@[simp] theorem mk_add (x y : IGame) : mk (x + y) = mk x + mk y := rfl
@[simp] theorem mk_neg (x : IGame) : mk (-x) = -mk x := rfl
@[simp] theorem mk_sub (x y : IGame) : mk (x - y) = mk x - mk y := rfl

@[simp] theorem mk_le_mk {x y : IGame} : mk x ≤ mk y ↔ x ≤ y := Iff.rfl
@[simp] theorem mk_lt_mk {x y : IGame} : mk x < mk y ↔ x < y := Iff.rfl
@[simp] theorem mk_equiv_mk {x y : IGame} : mk x ≈ mk y ↔ x ≈ y := Iff.rfl

@[simp]
theorem mk_natCast : ∀ n : ℕ, mk n = n
  | 0 => rfl
  | n + 1 => by rw [Nat.cast_add, Nat.cast_add, mk_add, mk_natCast]; rfl

end Game
end
