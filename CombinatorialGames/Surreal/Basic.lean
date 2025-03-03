/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kim Morrison, Violeta Hernández Palacios
-/
import CombinatorialGames.IGame.Basic
import Mathlib.Algebra.Order.Hom.Monoid

/-!
# Surreal numbers

The basic theory of surreal numbers, built on top of the theory of combinatorial (pre-)games.

A pregame is `Numeric` if all the Left options are strictly smaller than all the Right options, and
all those options are themselves numeric. In terms of combinatorial games, the numeric games have
"frozen"; you can only make your position worse by playing, and Left is some definite "number" of
moves ahead (or behind) Right.

A surreal number is an equivalence class of numeric games.

Surreal numbers inherit the relations `≤` and `<` from games, and these relations satisfy the axioms
of a linear order. In fact, the surreals form a complete ordered field, containing a copy of the
reals, and much else besides!

## Algebraic operations

In this file, we show that the surreals form a linear ordered commutative group.

In `CombinatorialGames.Surreal.Multiplication`, we define multiplication and show that the surreals
form a linear ordered commutative ring.

## TODO

- Define the field structure on the surreals.
- Build the embedding from reals into surreals.
-/

universe u

noncomputable section

/-! ### Numeric games -/

namespace IGame

private def NumericAux (x : IGame) : Prop :=
  (∀ y ∈ x.leftMoves, ∀ z ∈ x.rightMoves, y < z) ∧
  (∀ y ∈ x.leftMoves, NumericAux y) ∧ (∀ y ∈ x.rightMoves, NumericAux y)
termination_by x
decreasing_by igame_wf

/-- A game `{s | t}ᴵ` is numeric if everything in `s` is less than everything in `t`, and all the
elements of these sets are also numeric.

The `Surreal` numbers are built as the quotient of numeric games under equivalence. -/
@[mk_iff numeric_iff_aux]
class Numeric (x : IGame) : Prop where
  out : NumericAux x

theorem numeric_def {x : IGame} : Numeric x ↔
    (∀ y ∈ x.leftMoves, ∀ z ∈ x.rightMoves, y < z) ∧
    (∀ y ∈ x.leftMoves, Numeric y) ∧ (∀ y ∈ x.rightMoves, Numeric y) := by
  simp_rw [numeric_iff_aux]; rw [NumericAux]

namespace Numeric
variable {x y z : IGame}

theorem mk' (h₁ : ∀ y ∈ x.leftMoves, ∀ z ∈ x.rightMoves, y < z)
    (h₂ : ∀ y ∈ x.leftMoves, Numeric y) (h₃ : ∀ y ∈ x.rightMoves, Numeric y) : Numeric x :=
  numeric_def.2 ⟨h₁, h₂, h₃⟩

theorem leftMove_lt_rightMove [h : Numeric x]
    (hy : y ∈ x.leftMoves) (hz : z ∈ x.rightMoves) : y < z :=
  (numeric_def.1 h).1 y hy z hz

protected theorem of_mem_leftMoves [h : Numeric x] (hy : y ∈ x.leftMoves) : Numeric y :=
  (numeric_def.1 h).2.1 y hy

protected theorem of_mem_rightMoves [h : Numeric x] (hy : y ∈ x.rightMoves) : Numeric y :=
  (numeric_def.1 h).2.2 y hy

protected theorem isOption [Numeric x] (h : IsOption y x) : Numeric y := by
  cases h with
  | inl h => exact Numeric.of_mem_leftMoves h
  | inr h => exact Numeric.of_mem_rightMoves h

@[simp]
protected instance zero : Numeric 0 := by
  rw [numeric_def]; simp

@[simp]
protected instance one : Numeric 1 := by
  rw [numeric_def]; simp

protected instance subtype (x : Subtype Numeric) : Numeric x.1 := x.2

protected theorem le_of_not_le {x y : IGame} [Numeric x] [Numeric y] : ¬ x ≤ y → y ≤ x := by
  rw [lf_iff_exists_le, le_iff_forall_lf]
  rintro (⟨z, hz, h⟩ | ⟨z, hz, h⟩) <;> constructor <;> intro a ha h'
  · have := Numeric.of_mem_leftMoves hz; have := Numeric.of_mem_leftMoves ha
    exact (leftMove_lf_of_le h' hz) (Numeric.le_of_not_le (leftMove_lf_of_le h ha))
  · exact (leftMove_lt_rightMove hz ha).not_le (h'.trans h)
  · exact (leftMove_lt_rightMove ha hz).not_le (h.trans h')
  · have := Numeric.of_mem_rightMoves hz; have := Numeric.of_mem_rightMoves ha
    exact (lf_rightMove_of_le h' hz) (Numeric.le_of_not_le (lf_rightMove_of_le h ha))
termination_by x
decreasing_by igame_wf

protected theorem le_total (x y : IGame) [Numeric x] [Numeric y] : x ≤ y ∨ y ≤ x := by
  rw [or_iff_not_imp_left]
  exact Numeric.le_of_not_le

protected theorem lt_of_not_le [Numeric x] [Numeric y] (h : ¬ x ≤ y) : y < x :=
  (Numeric.le_of_not_le h).lt_of_not_le h

@[simp]
protected theorem not_le [Numeric x] [Numeric y] : ¬ x ≤ y ↔ y < x :=
  ⟨Numeric.lt_of_not_le, not_le_of_lt⟩

@[simp]
protected theorem not_lt [Numeric x] [Numeric y] : ¬ x < y ↔ y ≤ x :=
  not_iff_comm.1 Numeric.not_le

theorem not_fuzzy [Numeric x] [Numeric y] : ¬ x ‖ y := by
  simpa using Numeric.le_total x y

theorem lt_or_equiv_or_gt [Numeric x] [Numeric y] : x < y ∨ x ≈ y ∨ y < x := by
  simp_rw [← Numeric.not_le]; tauto

theorem le_iff_forall_lt [Numeric x] [Numeric y] :
    x ≤ y ↔ (∀ z ∈ x.leftMoves, z < y) ∧ (∀ z ∈ y.rightMoves, x < z) := by
  rw [le_iff_forall_lf]
  congr! <;> rename_i z hz
  · have := Numeric.of_mem_leftMoves hz; rw [Numeric.not_le]
  · have := Numeric.of_mem_rightMoves hz; rw [Numeric.not_le]

theorem lt_iff_exists_le [Numeric x] [Numeric y] :
    x < y ↔ (∃ z ∈ y.leftMoves, x ≤ z) ∨ (∃ z ∈ x.rightMoves, z ≤ y) := by
  rw [← Numeric.not_le, lf_iff_exists_le]

theorem leftMove_lt [Numeric x] (h : y ∈ x.leftMoves) : y < x := by
  have := Numeric.of_mem_leftMoves h; simpa using leftMove_lf h

theorem lt_rightMove [Numeric x] (h : y ∈ x.rightMoves) : x < y := by
  have := Numeric.of_mem_rightMoves h; simpa using lf_rightMove h

protected instance neg (x : IGame) [Numeric x] : Numeric (-x) := by
  refine mk' (fun y hy z hz ↦ ?_) ?_ ?_
  · rw [← IGame.neg_lt_neg_iff]
    apply @leftMove_lt_rightMove x <;> simp_all
  all_goals
    intro y hy
    simp only [leftMoves_neg, rightMoves_neg] at hy
    try have := Numeric.of_mem_leftMoves hy
    try have := Numeric.of_mem_rightMoves hy
    simpa using Numeric.neg (-y)
termination_by x
decreasing_by all_goals simp_all; igame_wf

protected instance add (x y : IGame) [Numeric x] [Numeric y] : Numeric (x + y) := by
  apply mk' <;> simp only [leftMoves_add, rightMoves_add, Set.mem_union, Set.mem_image]
  · rintro _ (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) _ (⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩)
    any_goals simpa using leftMove_lt_rightMove ha hb
    all_goals
      trans (x + y)
      · simpa using leftMove_lt ha
      · simpa using lt_rightMove hb
  all_goals
    rintro _ (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
    all_goals
      try have := Numeric.of_mem_leftMoves hz;
      try have := Numeric.of_mem_rightMoves hz;
      exact Numeric.add ..
termination_by (x, y)
decreasing_by igame_wf

protected instance sub (x y : IGame) [Numeric x] [Numeric y] : Numeric (x - y) :=
  inferInstanceAs (Numeric (x + -y))

protected instance natCast : ∀ n : ℕ, Numeric n
  | 0 => inferInstanceAs (Numeric 0)
  | n + 1 => have := Numeric.natCast n; inferInstanceAs (Numeric (n + 1))

protected instance ofNat (n : ℕ) [n.AtLeastTwo] : Numeric ofNat(n) :=
  inferInstanceAs (Numeric n)

end Numeric
end IGame

/-! ### Surreal numbers -/

open IGame

/-- The type of surreal numbers. These are the numeric games quotiented by the antisymmetrization
relation `x ≈ y ↔ x ≤ y ∧ y ≤ x`. In the quotient, the order becomes a total order. -/
def Surreal : Type (u + 1) :=
  Antisymmetrization (Subtype Numeric) (· ≤ ·)

namespace Surreal

/-- The quotient map from the subtype of numeric `IGame`s into `Game`. -/
def mk (x : IGame) [h : Numeric x] : Surreal := Quotient.mk _ ⟨x, h⟩
theorem mk_eq_mk {x y : IGame} [Numeric x] [Numeric y] : mk x = mk y ↔ x ≈ y := Quotient.eq

alias ⟨_, mk_eq⟩ := mk_eq_mk

@[cases_eliminator]
theorem ind {P : Surreal → Prop} (H : ∀ y [Numeric y], P (mk y)) (x : Surreal) : P x :=
  Quotient.ind (fun h ↦ @H _ h.2) x

/-- Choose an element of the equivalence class using the axiom of choice. -/
def out (x : Surreal) : IGame := (Quotient.out x).1
@[simp] instance (x : Surreal) : Numeric x.out := (Quotient.out x).2
@[simp] theorem out_eq (x : Surreal) : mk x.out = x := Quotient.out_eq x

theorem mk_out_equiv (x : IGame) [h : Numeric x] : (mk x).out ≈ x :=
  Quotient.mk_out (s := AntisymmRel.setoid (Subtype _) (· ≤ ·)) ⟨x, h⟩

theorem equiv_mk_out (x : IGame) [Numeric x] : x ≈ (mk x).out :=
  (mk_out_equiv x).symm

instance : Zero Surreal := ⟨mk 0⟩
instance : One Surreal := ⟨mk 1⟩
instance : Inhabited Surreal := ⟨0⟩

instance : Add Surreal where
  add := Quotient.map₂ (fun a b ↦ ⟨a.1 + b.1, inferInstance⟩) fun _ _ h₁ _ _ h₂ ↦ add_congr h₁ h₂

instance : Neg Surreal where
  neg := Quotient.map (fun a ↦ ⟨-a.1, inferInstance⟩) fun _ _ ↦ neg_congr

instance : PartialOrder Surreal :=
  inferInstanceAs (PartialOrder (Antisymmetrization ..))

instance : LinearOrderedAddCommGroup Surreal where
  zero_add := by rintro ⟨x⟩; change mk (0 + _) = mk _; simp_rw [zero_add]
  add_zero := by rintro ⟨x⟩; change mk (_ + 0) = mk _; simp_rw [add_zero]
  add_comm := by rintro ⟨x⟩ ⟨y⟩; change mk (_ + _) = mk (_ + _); simp_rw [add_comm]
  add_assoc := by rintro ⟨x⟩ ⟨y⟩ ⟨z⟩; change mk (_ + _ + _) = mk (_ + (_ + _)); simp_rw [add_assoc]
  neg_add_cancel := by rintro ⟨a⟩; exact mk_eq (neg_add_equiv _)
  add_le_add_left := by rintro ⟨a⟩ ⟨b⟩ h ⟨c⟩; exact add_le_add_left (α := IGame) h _
  le_total := by rintro ⟨x⟩ ⟨y⟩; exact Numeric.le_total x y
  decidableLE := Classical.decRel _
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : AddMonoidWithOne Surreal where

@[simp] theorem mk_zero : mk 0 = 0 := rfl
@[simp] theorem mk_one : mk 1 = 1 := rfl
@[simp] theorem mk_add (x y : IGame) [Numeric x] [Numeric y] : mk (x + y) = mk x + mk y := rfl
@[simp] theorem mk_neg (x : IGame) [Numeric x] : mk (-x) = -mk x := rfl
@[simp] theorem mk_sub (x y : IGame) [Numeric x] [Numeric y] : mk (x - y) = mk x - mk y := rfl

@[simp] theorem mk_le_mk {x y : IGame} [Numeric x] [Numeric y] : mk x ≤ mk y ↔ x ≤ y := Iff.rfl
@[simp] theorem mk_lt_mk {x y : IGame} [Numeric x] [Numeric y] : mk x < mk y ↔ x < y := Iff.rfl

/-- Casts a `Surreal` number into a `Game`. -/
def toGame : Surreal ↪o Game where
  toFun := Quotient.lift (fun x ↦ .mk x) fun _ _ ↦ Game.mk_eq
  inj' x y := by
    cases x; cases y;
    change Game.mk _ = Game.mk _ → _
    simp [Game.mk_eq_mk, mk_eq_mk]
  map_rel_iff' := by rintro ⟨_⟩ ⟨_⟩; rfl

@[simp] theorem toGame_mk (x : IGame) [Numeric x] : toGame (mk x) = .mk x := rfl
@[simp] theorem toGame_zero : toGame 0 = 0 := rfl
@[simp] theorem toGame_one : toGame 1 = 1 := rfl

theorem toGame_le_iff {a b : Surreal} : toGame a ≤ toGame b ↔ a ≤ b := by simp
theorem toGame_lt_iff {a b : Surreal} : toGame a < toGame b ↔ a < b := by simp
theorem toGame_inj {a b : Surreal} : toGame a = toGame b ↔ a = b := by simp

/-- `Surreal.toGame` as an `OrderAddMonoidHom` -/
@[simps]
def toGameAddHom : Surreal →+o Game where
  toFun := toGame
  map_zero' := rfl
  map_add' := by rintro ⟨_⟩ ⟨_⟩; rfl
  monotone' := toGame.monotone

@[simp]
theorem toGame_add (x y : Surreal) : toGame (x + y) = toGame x + toGame y :=
  toGameAddHom.map_add x y

@[simp]
theorem toGame_neg (x : Surreal) : toGame (-x) = -toGame x :=
  toGameAddHom.map_neg x

@[simp]
theorem toGame_sub (x y : Surreal) : toGame (x - y) = toGame x - toGame y :=
  toGameAddHom.map_sub x y

@[simp]
theorem toGame_natCast (n : ℕ) : toGame n = n :=
  map_natCast' toGameAddHom rfl n

end Surreal
end
