/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kim Morrison
-/
import CombinatorialGames.IGame.Basic

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
  apply mk'
  · simp_rw [leftMoves_add, rightMoves_add, Set.mem_union, Set.mem_image]
    rintro _ (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) _ (⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩)
    · rw [add_lt_add_iff_right]

#exit

theorem sub {x y : PGame} (ox : Numeric x) (oy : Numeric y) : Numeric (x - y) :=
  ox.add oy.neg

#exit

end Numeric
  #exit



namespace Numeric

theorem moveLeft_lt {x : PGame} (o : Numeric x) (i) : x.moveLeft i < x :=
  (moveLeft_lf i).lt (o.moveLeft i) o

theorem moveLeft_le {x : PGame} (o : Numeric x) (i) : x.moveLeft i ≤ x :=
  (o.moveLeft_lt i).le

theorem lt_moveRight {x : PGame} (o : Numeric x) (j) : x < x.moveRight j :=
  (lf_moveRight j).lt o (o.moveRight j)

theorem le_moveRight {x : PGame} (o : Numeric x) (j) : x ≤ x.moveRight j :=
  (o.lt_moveRight j).le

theorem add : ∀ {x y : PGame} (_ : Numeric x) (_ : Numeric y), Numeric (x + y)
  | ⟨xl, xr, xL, xR⟩, ⟨yl, yr, yL, yR⟩, ox, oy =>
    ⟨by
      rintro (ix | iy) (jx | jy)
      · exact add_lt_add_right (ox.1 ix jx) _
      · exact (add_lf_add_of_lf_of_le (lf_mk _ _ ix) (oy.le_moveRight jy)).lt
          ((ox.moveLeft ix).add oy) (ox.add (oy.moveRight jy))
      · exact (add_lf_add_of_lf_of_le (mk_lf _ _ jx) (oy.moveLeft_le iy)).lt
          (ox.add (oy.moveLeft iy)) ((ox.moveRight jx).add oy)
      · exact add_lt_add_left (oy.1 iy jy) ⟨xl, xr, xL, xR⟩, by
      constructor
      · rintro (ix | iy)
        · exact (ox.moveLeft ix).add oy
        · exact ox.add (oy.moveLeft iy)
      · rintro (jx | jy)
        · apply (ox.moveRight jx).add oy
        · apply ox.add (oy.moveRight jy)⟩
termination_by x y => (x, y)

theorem sub {x y : PGame} (ox : Numeric x) (oy : Numeric y) : Numeric (x - y) :=
  ox.add oy.neg

end Numeric

/-- Pre-games defined by natural numbers are numeric. -/
theorem numeric_nat : ∀ n : ℕ, Numeric n
  | 0 => numeric_zero
  | n + 1 => (numeric_nat n).add numeric_one

end PGame

open PGame

/-- The type of surreal numbers. These are the numeric pre-games quotiented
by the equivalence relation `x ≈ y ↔ x ≤ y ∧ y ≤ x`. In the quotient,
the order becomes a total order. -/
def Surreal :=
  Quotient (inferInstanceAs <| Setoid (Subtype Numeric))

namespace Surreal

/-- Construct a surreal number from a numeric pre-game. -/
def mk (x : PGame) (h : x.Numeric) : Surreal :=
  ⟦⟨x, h⟩⟧

instance : Zero Surreal :=
  ⟨mk 0 numeric_zero⟩

instance : One Surreal :=
  ⟨mk 1 numeric_one⟩

instance : Inhabited Surreal :=
  ⟨0⟩

lemma mk_eq_mk {x y : PGame.{u}} {hx hy} : mk x hx = mk y hy ↔ x ≈ y := Quotient.eq
alias ⟨_, mk_eq⟩ := mk_eq_mk

lemma mk_eq_zero {x : PGame.{u}} {hx} : mk x hx = 0 ↔ x ≈ 0 := Quotient.eq

/-- Lift an equivalence-respecting function on pre-games to surreals. -/
def lift {α} (f : ∀ x, Numeric x → α)
    (H : ∀ {x y} (hx : Numeric x) (hy : Numeric y), x ≈ y → f x hx = f y hy) : Surreal → α :=
  Quotient.lift (fun x : { x // Numeric x } ↦ f x.1 x.2) fun x y ↦ H x.2 y.2

/-- Lift a binary equivalence-respecting function on pre-games to surreals. -/
def lift₂ {α} (f : ∀ x y, Numeric x → Numeric y → α)
    (H :
      ∀ {x₁ y₁ x₂ y₂} (ox₁ : Numeric x₁) (oy₁ : Numeric y₁) (ox₂ : Numeric x₂) (oy₂ : Numeric y₂),
        x₁ ≈ x₂ → y₁ ≈ y₂ → f x₁ y₁ ox₁ oy₁ = f x₂ y₂ ox₂ oy₂) :
    Surreal → Surreal → α :=
  lift (fun x ox ↦ lift (fun y oy ↦ f x y ox oy) fun _ _ ↦ H _ _ _ _ .rfl)
    fun _ _ h ↦ funext <| Quotient.ind fun _ ↦ H _ _ _ _ h .rfl

instance instLE : LE Surreal :=
  ⟨lift₂ (fun x y _ _ ↦ x ≤ y) fun _ _ _ _ hx hy ↦ propext (hx.le_congr hy)⟩

@[simp]
lemma mk_le_mk {x y : PGame.{u}} {hx hy} : mk x hx ≤ mk y hy ↔ x ≤ y := Iff.rfl

lemma zero_le_mk {x : PGame.{u}} {hx} : 0 ≤ mk x hx ↔ 0 ≤ x := Iff.rfl

instance instLT : LT Surreal :=
  ⟨lift₂ (fun x y _ _ ↦ x < y) fun _ _ _ _ hx hy ↦ propext (hx.lt_congr hy)⟩

lemma mk_lt_mk {x y : PGame.{u}} {hx hy} : mk x hx < mk y hy ↔ x < y := Iff.rfl

lemma zero_lt_mk {x : PGame.{u}} {hx} : 0 < mk x hx ↔ 0 < x := Iff.rfl

/-- Same as `moveLeft_lt`, but for `Surreal` instead of `PGame` -/
theorem mk_moveLeft_lt_mk {x : PGame} (o : Numeric x) (i) :
    Surreal.mk (x.moveLeft i) (Numeric.moveLeft o i) < Surreal.mk x o := Numeric.moveLeft_lt o i

/-- Same as `lt_moveRight`, but for `Surreal` instead of `PGame` -/
theorem mk_lt_mk_moveRight {x : PGame} (o : Numeric x) (j) :
    Surreal.mk x o < Surreal.mk (x.moveRight j) (Numeric.moveRight o j) := Numeric.lt_moveRight o j

/-- Addition on surreals is inherited from pre-game addition:
the sum of `x = {xL | xR}` and `y = {yL | yR}` is `{xL + y, x + yL | xR + y, x + yR}`. -/
instance : Add Surreal :=
  ⟨Surreal.lift₂ (fun (x y : PGame) ox oy ↦ ⟦⟨x + y, ox.add oy⟩⟧) fun _ _ _ _ hx hy ↦
      Quotient.sound (add_congr hx hy)⟩

/-- Negation for surreal numbers is inherited from pre-game negation:
the negation of `{L | R}` is `{-R | -L}`. -/
instance : Neg Surreal :=
  ⟨Surreal.lift (fun x ox ↦ ⟦⟨-x, ox.neg⟩⟧) fun _ _ a ↦ Quotient.sound (neg_equiv_neg_iff.2 a)⟩

instance orderedAddCommGroup : OrderedAddCommGroup Surreal where
  add := (· + ·)
  add_assoc := by rintro ⟨_⟩ ⟨_⟩ ⟨_⟩; exact Quotient.sound add_assoc_equiv
  zero := 0
  zero_add := by rintro ⟨a⟩; exact Quotient.sound (zero_add_equiv a)
  add_zero := by rintro ⟨a⟩; exact Quotient.sound (add_zero_equiv a)
  neg := Neg.neg
  neg_add_cancel := by rintro ⟨a⟩; exact Quotient.sound (neg_add_cancel_equiv a)
  add_comm := by rintro ⟨_⟩ ⟨_⟩; exact Quotient.sound add_comm_equiv
  le := (· ≤ ·)
  lt := (· < ·)
  le_refl := by rintro ⟨_⟩; apply @le_rfl PGame
  le_trans := by rintro ⟨_⟩ ⟨_⟩ ⟨_⟩; apply @le_trans PGame
  lt_iff_le_not_le := by rintro ⟨_, ox⟩ ⟨_, oy⟩; apply @lt_iff_le_not_le PGame
  le_antisymm := by rintro ⟨_⟩ ⟨_⟩ h₁ h₂; exact Quotient.sound ⟨h₁, h₂⟩
  add_le_add_left := by rintro ⟨_⟩ ⟨_⟩ hx ⟨_⟩; exact @add_le_add_left PGame _ _ _ _ _ hx _
  nsmul := nsmulRec
  zsmul := zsmulRec

lemma mk_add {x y : PGame} (hx : x.Numeric) (hy : y.Numeric) :
    Surreal.mk (x + y) (hx.add hy) = Surreal.mk x hx + Surreal.mk y hy := by rfl

lemma mk_sub {x y : PGame} (hx : x.Numeric) (hy : y.Numeric) :
    Surreal.mk (x - y) (hx.sub hy) = Surreal.mk x hx - Surreal.mk y hy := by rfl

lemma zero_def : 0 = mk 0 numeric_zero := by rfl

noncomputable instance : LinearOrderedAddCommGroup Surreal :=
  { Surreal.orderedAddCommGroup with
    le_total := by
      rintro ⟨⟨x, ox⟩⟩ ⟨⟨y, oy⟩⟩
      exact or_iff_not_imp_left.2 fun h ↦ (PGame.not_le.1 h).le oy ox
    decidableLE := Classical.decRel _ }

instance : AddMonoidWithOne Surreal :=
  AddMonoidWithOne.unary

/-- Casts a `Surreal` number into a `Game`. -/
def toGame : Surreal →+o Game where
  toFun := lift (fun x _ ↦ ⟦x⟧) fun _ _ ↦ Quot.sound
  map_zero' := rfl
  map_add' := by rintro ⟨_, _⟩ ⟨_, _⟩; rfl
  monotone' := by rintro ⟨_, _⟩ ⟨_, _⟩; exact id

@[simp]
theorem zero_toGame : toGame 0 = 0 :=
  rfl

@[simp]
theorem one_toGame : toGame 1 = 1 :=
  rfl

@[simp]
theorem nat_toGame : ∀ n : ℕ, toGame n = n :=
  map_natCast' _ one_toGame

/-- A small family of surreals is bounded above. -/
lemma bddAbove_range_of_small {ι : Type*} [Small.{u} ι] (f : ι → Surreal.{u}) :
    BddAbove (Set.range f) := by
  induction' f using Quotient.induction_on_pi with f
  let g : ι → PGame.{u} := Subtype.val ∘ f
  have hg (i) : (g i).Numeric := Subtype.prop _
  conv in (⟦f _⟧) =>
    change mk (g i) (hg i)
  clear_value g
  clear f
  let x : PGame.{u} := ⟨Σ i, (g <| (equivShrink.{u} ι).symm i).LeftMoves, PEmpty,
    fun x ↦ moveLeft _ x.2, PEmpty.elim⟩
  refine ⟨mk x (.mk (by simp [x]) (fun _ ↦ (hg _).moveLeft _) (by simp [x])),
    Set.forall_mem_range.2 fun i ↦ ?_⟩
  rw [mk_le_mk, ← (equivShrink ι).symm_apply_apply i, le_iff_forall_lf]
  simpa [x] using fun j ↦ @moveLeft_lf x ⟨equivShrink ι i, j⟩

/-- A small set of surreals is bounded above. -/
lemma bddAbove_of_small (s : Set Surreal.{u}) [Small.{u} s] : BddAbove s := by
  simpa using bddAbove_range_of_small (Subtype.val : s → Surreal.{u})

/-- A small family of surreals is bounded below. -/
lemma bddBelow_range_of_small {ι : Type*} [Small.{u} ι] (f : ι → Surreal.{u}) :
    BddBelow (Set.range f) := by
  induction' f using Quotient.induction_on_pi with f
  let g : ι → PGame.{u} := Subtype.val ∘ f
  have hg (i) : (g i).Numeric := Subtype.prop _
  conv in (⟦f _⟧) =>
    change mk (g i) (hg i)
  clear_value g
  clear f
  let x : PGame.{u} := ⟨PEmpty, Σ i, (g <| (equivShrink.{u} ι).symm i).RightMoves,
    PEmpty.elim, fun x ↦ moveRight _ x.2⟩
  refine ⟨mk x (.mk (by simp [x]) (by simp [x]) (fun _ ↦ (hg _).moveRight _) ),
    Set.forall_mem_range.2 fun i ↦ ?_⟩
  rw [mk_le_mk, ← (equivShrink ι).symm_apply_apply i, le_iff_forall_lf]
  simpa [x] using fun j ↦ @lf_moveRight x ⟨equivShrink ι i, j⟩

/-- A small set of surreals is bounded below. -/
lemma bddBelow_of_small (s : Set Surreal.{u}) [Small.{u} s] : BddBelow s := by
  simpa using bddBelow_range_of_small (Subtype.val : s → Surreal.{u})

end Surreal

open Surreal
