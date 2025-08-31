/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kim Morrison, Violeta Hernández Palacios
-/
import CombinatorialGames.Game.Birthday
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

- Prove that surreals with finite birthday are dyadic rationals.
- Build the embedding from reals into surreals.
- Define sign sequences.
-/

universe u

noncomputable section

/-! ### Numeric games -/

namespace IGame

private def NumericAux (x : IGame) : Prop :=
  (∀ y ∈ xᴸ, ∀ z ∈ xᴿ, y < z) ∧ (∀ p, ∀ y ∈ x.moves p, NumericAux y)
termination_by x
decreasing_by igame_wf

/-- A game `!{s | t}` is numeric if everything in `s` is less than everything in `t`, and all the
elements of these sets are also numeric.

The `Surreal` numbers are built as the quotient of numeric games under equivalence. -/
@[mk_iff numeric_iff_aux]
class Numeric (x : IGame) : Prop where of_NumericAux ::
  out : NumericAux x

theorem numeric_def {x : IGame} : Numeric x ↔
    (∀ y ∈ xᴸ, ∀ z ∈ xᴿ, y < z) ∧ (∀ p, ∀ y ∈ x.moves p, Numeric y) := by
  simp_rw [numeric_iff_aux]; rw [NumericAux]

namespace Numeric
variable {x y z : IGame}

theorem mk (h₁ : ∀ y ∈ xᴸ, ∀ z ∈ xᴿ, y < z) (h₂ : ∀ p, ∀ y ∈ x.moves p, Numeric y) : Numeric x :=
  numeric_def.2 ⟨h₁, h₂⟩

theorem leftMove_lt_rightMove [h : Numeric x] (hy : y ∈ xᴸ) (hz : z ∈ xᴿ) : y < z :=
  (numeric_def.1 h).1 y hy z hz

protected theorem of_mem_moves {p : Player} [h : Numeric x] (hy : y ∈ x.moves p) : Numeric y :=
  (numeric_def.1 h).2 p y hy

protected theorem isOption [Numeric x] (h : IsOption y x) : Numeric y := by
  rw [isOption_iff_mem_union] at h
  cases h with
  | _ h => exact .of_mem_moves h

alias _root_.IGame.IsOption.numeric := Numeric.isOption

@[simp]
protected instance zero : Numeric 0 := by
  rw [numeric_def]; simp

@[simp]
protected instance one : Numeric 1 := by
  rw [numeric_def]; simp

@[simp]
protected instance half : Numeric ½ := by
  rw [numeric_def]; simp

protected instance subtype (x : Subtype Numeric) : Numeric x.1 := x.2

protected theorem le_of_not_le {x y : IGame} [Numeric x] [Numeric y] : ¬ x ≤ y → y ≤ x := by
  rw [lf_iff_exists_le, le_iff_forall_lf]
  rintro (⟨z, hz, h⟩ | ⟨z, hz, h⟩) <;> constructor <;> intro a ha h'
  · have := Numeric.of_mem_moves hz; have := Numeric.of_mem_moves ha
    exact (leftMove_lf_of_le h' hz) (Numeric.le_of_not_le (leftMove_lf_of_le h ha))
  · exact (leftMove_lt_rightMove hz ha).not_ge (h'.trans h)
  · exact (leftMove_lt_rightMove ha hz).not_ge (h.trans h')
  · have := Numeric.of_mem_moves hz; have := Numeric.of_mem_moves ha
    exact (lf_rightMove_of_le h' hz) (Numeric.le_of_not_le (lf_rightMove_of_le h ha))
termination_by x
decreasing_by igame_wf

protected theorem le_total (x y : IGame) [Numeric x] [Numeric y] : x ≤ y ∨ y ≤ x := by
  rw [or_iff_not_imp_left]
  exact Numeric.le_of_not_le

protected theorem lt_of_not_ge [Numeric x] [Numeric y] (h : ¬ x ≤ y) : y < x :=
  (Numeric.le_of_not_le h).lt_of_not_ge h

@[simp]
protected theorem not_le [Numeric x] [Numeric y] : ¬ x ≤ y ↔ y < x :=
  ⟨Numeric.lt_of_not_ge, not_le_of_gt⟩

@[simp]
protected theorem not_lt [Numeric x] [Numeric y] : ¬ x < y ↔ y ≤ x :=
  not_iff_comm.1 Numeric.not_le

protected theorem le_or_gt (x y : IGame) [Numeric x] [Numeric y] : x ≤ y ∨ y < x := by
  rw [← Numeric.not_le]
  exact em _

protected theorem lt_or_ge (x y : IGame) [Numeric x] [Numeric y] : x < y ∨ y ≤ x := by
  rw [← Numeric.not_lt]
  exact em _

theorem not_fuzzy (x y : IGame) [Numeric x] [Numeric y] : ¬ x ‖ y := by
  simpa [not_incompRel_iff] using Numeric.le_total x y

theorem lt_or_equiv_or_gt (x y : IGame) [Numeric x] [Numeric y] : x < y ∨ x ≈ y ∨ y < x := by
  simp_rw [← Numeric.not_le]; tauto

/-- To prove a game is numeric, it suffices to show the left options are less or fuzzy
to the right options.-/
theorem mk_of_lf (h₁ : ∀ y ∈ xᴸ, ∀ z ∈ xᴿ, y ⧏ z)
    (h₂ : ∀ p, ∀ y ∈ x.moves p, Numeric y) : Numeric x :=
  mk (fun y hy z hz ↦ (@Numeric.not_le z y (h₂ _ z hz) (h₂ _ y hy)).1 (h₁ y hy z hz)) h₂

theorem le_iff_forall_lt [Numeric x] [Numeric y] :
    x ≤ y ↔ (∀ z ∈ xᴸ, z < y) ∧ (∀ z ∈ yᴿ, x < z) := by
  rw [le_iff_forall_lf]
  congr! with z hz z hz
  · have := Numeric.of_mem_moves hz; rw [Numeric.not_le]
  · have := Numeric.of_mem_moves hz; rw [Numeric.not_le]

theorem lt_iff_exists_le [Numeric x] [Numeric y] :
    x < y ↔ (∃ z ∈ yᴸ, x ≤ z) ∨ (∃ z ∈ xᴿ, z ≤ y) := by
  rw [← Numeric.not_le, lf_iff_exists_le]

theorem leftMove_lt [Numeric x] (h : y ∈ xᴸ) : y < x := by
  have := Numeric.of_mem_moves h; simpa using leftMove_lf h

theorem lt_rightMove [Numeric x] (h : y ∈ xᴿ) : x < y := by
  have := Numeric.of_mem_moves h; simpa using lf_rightMove h

protected instance neg (x : IGame) [Numeric x] : Numeric (-x) := by
  refine mk (fun y hy z hz ↦ ?_) ?_
  · rw [← IGame.neg_lt_neg_iff]
    apply @leftMove_lt_rightMove x <;> simp_all
  · intro p y hy
    rw [moves_neg] at hy
    have := Numeric.of_mem_moves hy
    simpa using Numeric.neg (-y)
termination_by x
decreasing_by all_goals simp_all; igame_wf

@[simp]
theorem neg_iff {x : IGame} : Numeric (-x) ↔ Numeric x :=
  ⟨fun _ ↦ by simpa using Numeric.neg (-x), fun _ ↦ Numeric.neg x⟩

protected instance add (x y : IGame) [Numeric x] [Numeric y] : Numeric (x + y) := by
  apply mk <;> simp only [moves_add, Set.mem_union, Set.mem_image]
  · rintro _ (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) _ (⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩)
    any_goals simpa using leftMove_lt_rightMove ha hb
    all_goals
      trans (x + y)
      · simpa using leftMove_lt ha
      · simpa using lt_rightMove hb
  · rintro p _ (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
    all_goals
      have := Numeric.of_mem_moves hz
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

protected instance intCast : ∀ n : ℤ, Numeric n
  | .ofNat n => inferInstanceAs (Numeric n)
  | .negSucc n => inferInstanceAs (Numeric (-(n + 1)))

end Numeric

/-! ### Simplicity theorem -/

/-- `x` fits within `y` when `z ⧏ x` for every `z ∈ yᴸ`, and `y ⧏ z` for every
`z ∈ yᴿ`.

The simplicity theorem states that if a game fits a numeric game, but none of its options do, then
the games are equivalent. In particular, a numeric game is equivalent to the game of the least
birthday that fits in it -/
def Fits (x y : IGame) : Prop :=
  (∀ z ∈ yᴸ, z ⧏ x) ∧ (∀ z ∈ yᴿ, x ⧏ z)

theorem fits_of_equiv {x y : IGame} (h : x ≈ y) : Fits x y :=
  ⟨fun _ hz ↦ not_le_of_not_le_of_le (leftMove_lf hz) h.ge,
    fun _ hz ↦ not_le_of_le_of_not_le h.le (lf_rightMove hz) ⟩

alias AntisymmRel.Fits := fits_of_equiv

theorem Fits.refl (x : IGame) : x.Fits x :=
  fits_of_equiv .rfl

@[simp]
theorem fits_neg_iff {x y : IGame} : Fits (-x) (-y) ↔ Fits x y := by
  rw [Fits, forall_moves_neg, forall_moves_neg, and_comm]; simp [Fits]

alias ⟨_, Fits.neg⟩ := fits_neg_iff

theorem not_fits_iff {x y : IGame} :
    ¬ Fits x y ↔ (∃ z ∈ yᴸ, x ≤ z) ∨ (∃ z ∈ yᴿ, z ≤ x) := by
  rw [Fits, not_and_or]; simp

theorem Fits.le_of_forall_leftMoves_not_fits {x y : IGame} [Numeric x] (hx : x.Fits y)
    (hl : ∀ z ∈ xᴸ, ¬ z.Fits y) : x ≤ y := by
  simp_rw [not_fits_iff] at hl
  refine le_iff_forall_lf.2 ⟨fun z hz ↦ ?_, hx.2⟩
  obtain (⟨w, hw, hw'⟩ | ⟨w, hw, hw'⟩) := hl z hz
  · exact not_le_of_le_of_not_le hw' (leftMove_lf hw)
  · cases hx.2 w hw <| (hw'.trans_lt (Numeric.leftMove_lt hz)).le

theorem Fits.le_of_forall_rightMoves_not_fits {x y : IGame} [Numeric x] (hx : x.Fits y)
    (hr : ∀ z ∈ xᴿ, ¬ z.Fits y) : y ≤ x := by
  rw [← IGame.neg_le_neg_iff]
  apply hx.neg.le_of_forall_leftMoves_not_fits
  simpa only [fits_neg_iff, forall_moves_neg]

/-- A variant of the **simplicity theorem**: if a numeric game `x` fits within a game `y`, but none
of its options do, then `x ≈ y`. -/
theorem Fits.equiv_of_forall_not_fits {x y : IGame} [Numeric x] (hx : x.Fits y)
    (hl : ∀ z ∈ xᴸ, ¬ z.Fits y) (hr : ∀ z ∈ xᴿ, ¬ z.Fits y) : x ≈ y :=
  ⟨hx.le_of_forall_leftMoves_not_fits hl, hx.le_of_forall_rightMoves_not_fits hr⟩

/-- A variant of the **simplicity theorem**: if `x` is the numeric game with the least birthday that
fits within `y`, then `x ≈ y`. -/
theorem Fits.equiv_of_forall_birthday_le {x y : IGame} [Numeric x] (hx : x.Fits y)
    (H : ∀ z, Numeric z → z.Fits y → x.birthday ≤ z.birthday) : x ≈ y := by
  apply hx.equiv_of_forall_not_fits <;>
    exact fun z hz h ↦ (birthday_lt_of_mem_moves hz).not_ge <| H z (.of_mem_moves hz) h

/-- A specialization of the simplicity theorem to `0`. -/
theorem fits_zero_iff_equiv {x : IGame} [Numeric x] : Fits 0 x ↔ x ≈ 0 := by
  refine ⟨fun hx ↦ (hx.equiv_of_forall_not_fits ?_ ?_).symm, fun h ↦ fits_of_equiv h.symm⟩ <;> simp

/-- A specialization of the simplicity theorem to `1`. -/
theorem equiv_one_of_fits {x : IGame} [Numeric x] (hx : Fits 1 x) (h : ¬ x ≈ 0) : x ≈ 1 := by
  apply (hx.equiv_of_forall_not_fits _ _).symm
  · simpa [fits_zero_iff_equiv]
  · simp

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
theorem ind {motive : Surreal → Prop} (mk : ∀ y [Numeric y], motive (mk y)) (x : Surreal) :
    motive x := Quotient.ind (fun h ↦ @mk _ h.2) x

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

instance : LinearOrder Surreal where
  le_total := by rintro ⟨x⟩ ⟨y⟩; exact Numeric.le_total x y
  toDecidableLE := Classical.decRel _

instance : AddCommGroup Surreal where
  zero_add := by rintro ⟨x⟩; change mk (0 + x) = mk x; simp_rw [zero_add]
  add_zero := by rintro ⟨x⟩; change mk (x + 0) = mk x; simp_rw [add_zero]
  add_comm := by rintro ⟨x⟩ ⟨y⟩; change mk (x + y) = mk (y + x); simp_rw [add_comm]
  add_assoc := by rintro ⟨x⟩ ⟨y⟩ ⟨z⟩; change mk (x + y + z) = mk (x + (y + z)); simp_rw [add_assoc]
  neg_add_cancel := by rintro ⟨a⟩; exact mk_eq (neg_add_equiv _)
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : AddGroupWithOne Surreal where

instance : IsOrderedAddMonoid Surreal where
  add_le_add_left := by rintro ⟨a⟩ ⟨b⟩ h ⟨c⟩; exact add_le_add_left (α := IGame) h _

@[simp] theorem mk_zero : mk 0 = 0 := rfl
@[simp] theorem mk_one : mk 1 = 1 := rfl
@[simp] theorem mk_add (x y : IGame) [Numeric x] [Numeric y] : mk (x + y) = mk x + mk y := rfl
@[simp] theorem mk_neg (x : IGame) [Numeric x] : mk (-x) = -mk x := rfl
@[simp] theorem mk_sub (x y : IGame) [Numeric x] [Numeric y] : mk (x - y) = mk x - mk y := rfl

@[simp] theorem mk_le_mk {x y : IGame} [Numeric x] [Numeric y] : mk x ≤ mk y ↔ x ≤ y := Iff.rfl
@[simp] theorem mk_lt_mk {x y : IGame} [Numeric x] [Numeric y] : mk x < mk y ↔ x < y := Iff.rfl

@[simp]
theorem mk_natCast : ∀ n : ℕ, mk n = n
  | 0 => rfl
  | n + 1 => by simp_rw [Nat.cast_add_one, mk_add, mk_one, mk_natCast n]

@[simp]
theorem mk_intCast (n : ℤ) : mk n = n := by
  cases n <;> simp

instance : ZeroLEOneClass Surreal where
  zero_le_one := zero_le_one (α := IGame)

instance : NeZero (1 : Surreal) where
  out := by apply ne_of_gt; exact IGame.zero_lt_one

instance : Nontrivial Surreal :=
  ⟨_, _, zero_ne_one⟩

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

@[simp] theorem toGame_natCast (n : ℕ) : toGame n = n := map_natCast' toGameAddHom rfl n
@[simp] theorem toGame_intCast (n : ℤ) : toGame n = n := map_intCast' toGameAddHom rfl n

@[simp]
theorem game_out_eq (x : Surreal) : Game.mk x.out = x.toGame := by
  cases x
  rw [toGame_mk, Game.mk_eq_mk]
  exact mk_out_equiv _

/-- Construct a `Surreal` from its left and right sets, and a proof that all elements from the left
set are less than all the elements of the right set.

Note that although this function is well-defined, this function isn't injective, nor do equivalence
classes in Surreal have a canonical representative. (Note however that every short numeric game has
a unique "canonical" form!) -/
instance : OfSets Surreal.{u} (fun st ↦ ∀ x ∈ st left, ∀ y ∈ st right, x < y) where
  ofSets st H _ _ := by
    refine @mk !{fun p ↦ out '' st p} (.mk ?_ (by simp))
    rw [moves_ofSets, moves_ofSets]
    rintro - ⟨x, hx, rfl⟩ - ⟨y, hy, rfl⟩
    rw [← Surreal.mk_lt_mk, out_eq, out_eq]
    exact H x hx y hy

theorem toGame_ofSets' (st : Player → Set Surreal.{u}) [Small.{u} (st left)] [Small.{u} (st right)]
    {H : ∀ x ∈ st left, ∀ y ∈ st right, x < y} :
    toGame !{st} = !{fun p ↦ toGame '' st p} := by
  change toGame (@mk _ (_)) = _
  simp_rw [toGame_mk, Game.mk_ofSets', Set.image_image, game_out_eq]

@[simp]
theorem toGame_ofSets (s t : Set Surreal.{u}) [Small.{u} s] [Small.{u} t]
    {H : ∀ x ∈ s, ∀ y ∈ t, x < y} :
    toGame !{s | t} = !{toGame '' s | toGame '' t} := by
  rw [toGame_ofSets']
  congr; aesop

theorem mk_ofSets' {st : Player → Set IGame.{u}}
    [Small.{u} (st left)] [Small.{u} (st right)] {H : Numeric !{st}} :
    mk !{st} =
      !{fun p ↦ .range fun x : st p ↦ mk x (h := H.of_mem_moves (p := p) (by simp))}'
      (by have := @H.leftMove_lt_rightMove; aesop) := by
  change _ = @mk _ (_)
  simp_rw [← toGame_inj, toGame_mk, Game.mk_ofSets']
  congr; aesop

theorem mk_ofSets {s t : Set IGame.{u}} [Small.{u} s] [Small.{u} t] {H : Numeric !{s | t}} :
    mk !{s | t} =
      !{.range fun x : s ↦ mk x (h := H.of_mem_moves (p := left) (by simp)) |
        .range fun x : t ↦ mk x (h := H.of_mem_moves (p := right) (by simp))}'
      (by have := @H.leftMove_lt_rightMove; aesop) := by
  rw [mk_ofSets']
  congr!; aesop

@[aesop apply unsafe]
theorem lt_ofSets_of_mem_left {s t : Set Surreal.{u}} [Small.{u} s] [Small.{u} t]
    {H : ∀ x ∈ s, ∀ y ∈ t, x < y} {x : Surreal} (hx : x ∈ s) :
    x < !{s | t} := by
  rw [lt_iff_not_ge, ← toGame_le_iff, toGame_ofSets]
  exact Game.lf_ofSets_of_mem_left (Set.mem_image_of_mem _ hx)

@[aesop apply unsafe]
theorem ofSets_lt_of_mem_right {s t : Set Surreal.{u}} [Small.{u} s] [Small.{u} t]
    {H : ∀ x ∈ s, ∀ y ∈ t, x < y} {x : Surreal} (hx : x ∈ t) :
    !{s | t} < x := by
  rw [lt_iff_not_ge, ← toGame_le_iff, toGame_ofSets]
  exact Game.ofSets_lf_of_mem_right (Set.mem_image_of_mem _ hx)

theorem zero_def : (0 : Surreal) = !{fun _ ↦ ∅} := by apply (mk_ofSets' ..).trans; congr!; simp
theorem one_def : (1 : Surreal) = !{{0} | ∅} := by apply (mk_ofSets ..).trans; congr! <;> aesop

instance : DenselyOrdered Surreal where
  dense a b hab := ⟨!{{a} | {b}},
    lt_ofSets_of_mem_left (Set.mem_singleton a), ofSets_lt_of_mem_right (Set.mem_singleton b)⟩

end Surreal
end
