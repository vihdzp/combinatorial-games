/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Reid Barton, Mario Carneiro, Isabel Longbottom, Kim Morrison, Apurva Nakade, Yuyang Zhao
-/
import CombinatorialGames.Game.IGame
import Mathlib.Tactic.Abel

/-!
# Combinatorial games

In this file we construct the quotient of games `IGame` under equivalence, and prove that it forms
an `OrderedAddCommGroup`. We take advantage of this structure to prove two particularly tedious
theorems on `IGame`, namely `IGame.mul_add_equiv` and `IGame.mul_assoc_equiv`.

It might be tempting to write `mk (x * y)` as `mk x * mk y`, but the latter is not well-defined, as
there exist `x₁ ≈ x₂` and `y₁ ≈ y₂` with `x₁ * y₁ ≉ x₂ * y₂`. See
`CombinatorialGames.Counterexamples.Multiplication` for a proof.
-/

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

Note that although this function is well-defined, this function isn't injective, nor do equivalence
classes in `Game` have a canonical representative.  -/
def ofSets (s t : Set Game.{u}) [Small.{u} s] [Small.{u} t] : Game.{u} :=
  mk {out '' s | out '' t}ᴵ

@[inherit_doc] notation "{" s " | " t "}ᴳ" => ofSets s t

@[simp]
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
  zero_add := by rintro ⟨x⟩; change mk (0 + _) = mk _; rw [zero_add]
  add_zero := by rintro ⟨x⟩; change mk (_ + 0) = mk _; rw [add_zero]
  add_comm := by rintro ⟨x⟩ ⟨y⟩; change mk (_ + _) = mk (_ + _); rw [add_comm]
  add_assoc := by rintro ⟨x⟩ ⟨y⟩ ⟨z⟩; change mk (_ + _ + _) = mk (_ + (_ + _)); rw [add_assoc]
  neg_add_cancel := by rintro ⟨a⟩; exact mk_eq (neg_add_equiv _)
  add_le_add_left := by rintro ⟨a⟩ ⟨b⟩ h ⟨c⟩; exact add_le_add_left (α := IGame) h _
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : AddCommGroupWithOne Game where

@[simp] theorem mk_zero : mk 0 = 0 := rfl
@[simp] theorem mk_one : mk 1 = 1 := rfl
@[simp] theorem mk_add (x y : IGame) : mk (x + y) = mk x + mk y := rfl
@[simp] theorem mk_neg (x : IGame) : mk (-x) = -mk x := rfl
@[simp] theorem mk_sub (x y : IGame) : mk (x - y) = mk x - mk y := rfl

theorem mk_mulOption (x y a b : IGame) :
    mk (mulOption x y a b) = mk (a * y) + mk (x * b) - mk (a * b) :=
  rfl

@[simp] theorem mk_le_mk {x y : IGame} : mk x ≤ mk y ↔ x ≤ y := Iff.rfl
@[simp] theorem mk_lt_mk {x y : IGame} : mk x < mk y ↔ x < y := Iff.rfl

@[simp]
theorem mk_natCast : ∀ n : ℕ, mk n = n
  | 0 => rfl
  | n + 1 => by rw [Nat.cast_add, Nat.cast_add, mk_add, mk_natCast]; rfl

@[simp]
theorem mk_intCast (n : ℤ) : mk n = n := by
  cases n <;> simp

theorem zero_def : 0 = {∅ | ∅}ᴳ := by apply (mk_ofSets _ _).trans; simp
theorem one_def : 1 = {{0} | ∅}ᴳ := by apply (mk_ofSets _ _).trans; simp

instance : ZeroLEOneClass Game where
  zero_le_one := zero_le_one (α := IGame)

instance : NeZero (1 : Game) where
  out := by apply ne_of_gt; exact IGame.zero_lt_one

instance : Nontrivial Game :=
  ⟨_, _, zero_ne_one⟩

-- https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/OrderedAddCommGroup.20has.20CharZero/near/506296353
instance {α : Type*} [AddMonoidWithOne α] [PartialOrder α] [ZeroLEOneClass α] [NeZero (1 : α)]
  [AddLeftStrictMono α] : CharZero α where
  cast_injective :=
    (strictMono_nat_of_lt_succ fun n ↦ by rw [Nat.cast_succ]; apply lt_add_one).injective

theorem mk_mul_add (x y z : IGame) : mk (x * (y + z)) = mk (x * y) + mk (x * z) := by
  rw [← mk_add, add_eq (x * y), mul_eq]
  simp only [leftMoves_add, rightMoves_add, leftMoves_mul, rightMoves_mul, prod_union,
    union_assoc, image_image, image_union, mk_ofSets]
  congr 1
  all_goals
    nth_rewrite 2 [union_left_comm]
    congr
    all_goals
      ext
      simp only [mulOption, mk_sub, mk_add, mem_image, mem_prod, and_assoc, Prod.exists,
        exists_and_left, exists_exists_and_eq_and]
      iterate 2 (congr! 2; rw [and_congr_right_iff]; intros)
      congr! 1
      rw [mk_mul_add, mk_mul_add, mk_mul_add]
      abel
termination_by (x, y, z)
decreasing_by igame_wf

theorem mk_mul_sub (x y z : IGame) : mk (x * (y - z)) = mk (x * y) - mk (x * z) := by
  simpa using mk_mul_add x y (-z)

theorem mk_add_mul (x y z : IGame) : mk ((x + y) * z) = mk (x * z) + mk (y * z) := by
  rw [mul_comm, mk_mul_add, mul_comm, mul_comm z]

theorem mk_sub_mul (x y z : IGame) : mk ((x - y) * z) = mk (x * z) - mk (y * z) := by
  simpa using mk_add_mul x (-y) z

-- TODO: upstream
theorem _root_.Set.prod_image_left {α β γ : Type*} (f : α → γ) (s : Set α) (t : Set β) :
    (f '' s) ×ˢ t = (fun x ↦ (f x.1, x.2)) '' s ×ˢ t := by
  aesop

-- TODO: upstream
theorem _root_.Set.prod_image_right {α β γ : Type*} (f : α → γ) (s : Set α) (t : Set β) :
    t ×ˢ (f '' s) = (fun x ↦ (x.1, f x.2)) '' t ×ˢ s := by
  aesop

set_option maxHeartbeats 1000000 in
theorem mk_mul_assoc (x y z : IGame) : mk (x * y * z) = mk (x * (y * z)) := by
  rw [mul_eq, mul_eq x (y * z)]
  simp only [leftMoves_mul, rightMoves_mul, union_prod, prod_union, union_assoc,
    image_image, image_union, mk_ofSets]
  congr 1
  all_goals
    nth_rewrite 2 [union_left_comm]
    nth_rewrite 3 [union_comm]
    congr
    all_goals
      simp_rw [prod_image_left, prod_image_right, image_image]
      ext
      simp only [mem_image, mem_prod, and_assoc, Prod.exists, exists_and_left]
      iterate 3 (congr! 2; rw [and_congr_right_iff]; intros)
      simp only [mulOption, mk_mul_add, mk_add_mul, mk_mul_sub, mk_sub_mul, mk_add, mk_sub]
      iterate 7 rw [mk_mul_assoc]
      abel_nf
termination_by (x, y, z)
decreasing_by igame_wf

end Game

namespace IGame

protected theorem sub_le_iff_le_add {x y z : IGame} : x - z ≤ y ↔ x ≤ y + z :=
  @sub_le_iff_le_add Game _ _ _ (.mk x) (.mk y) (.mk z)

protected theorem le_sub_iff_add_le {x y z : IGame} : x ≤ z - y ↔ x + y ≤ z :=
  @le_sub_iff_add_le Game _ _ _ (.mk x) (.mk y) (.mk z)

protected theorem sub_lt_iff_lt_add {x y z : IGame} : x - z < y ↔ x < y + z :=
  @sub_lt_iff_lt_add Game _ _ _ (.mk x) (.mk y) (.mk z)

protected theorem lt_sub_iff_add_lt {x y z : IGame} : x < z - y ↔ x + y < z :=
  @lt_sub_iff_add_lt Game _ _ _ (.mk x) (.mk y) (.mk z)

protected theorem sub_nonneg {x y : IGame} : 0 ≤ x - y ↔ y ≤ x :=
  @sub_nonneg Game _ _ _ (.mk x) (.mk y)

protected theorem sub_nonpos {x y : IGame} : x - y ≤ 0 ↔ x ≤ y :=
  @sub_nonpos Game _ _ _ (.mk x) (.mk y)

protected theorem sub_pos {x y : IGame} : 0 < x - y ↔ y < x :=
  @sub_pos Game _ _ _ (.mk x) (.mk y)

protected theorem sub_neg {x y : IGame} : x - y < 0 ↔ x < y :=
  @sub_neg Game _ _ _ (.mk x) (.mk y)

theorem mul_add_equiv (x y z : IGame) : x * (y + z) ≈ x * y + x * z :=
  Game.mk_eq_mk.1 (Game.mk_mul_add x y z)

theorem mul_sub_equiv (x y z : IGame) : x * (y - z) ≈ x * y - x * z :=
  Game.mk_eq_mk.1 (Game.mk_mul_sub x y z)

theorem add_mul_equiv (x y z : IGame) : (x + y) * z ≈ x * z + y * z :=
  Game.mk_eq_mk.1 (Game.mk_add_mul x y z)

theorem sub_mul_equiv (x y z : IGame) : (x - y) * z ≈ x * z - y * z :=
  Game.mk_eq_mk.1 (Game.mk_sub_mul x y z)

theorem mul_assoc_equiv (x y z : IGame) : x * y * z ≈ x * (y * z) :=
  Game.mk_eq_mk.1 (Game.mk_mul_assoc x y z)

@[simp]
theorem natCast_le {m n : ℕ} : (m : IGame) ≤ n ↔ m ≤ n := by
  simp [← Game.mk_le_mk]

@[simp]
theorem natCast_lt {m n : ℕ} : (m : IGame) < n ↔ m < n := by
  simp [← Game.mk_le_mk]

theorem natCast_strictMono : StrictMono ((↑) : ℕ → IGame) :=
  fun _ _ h ↦ natCast_lt.2 h

@[simp]
theorem natCast_inj {m n : ℕ} : (m : IGame) = n ↔ m = n :=
  natCast_strictMono.injective.eq_iff

@[simp]
theorem intCast_le {m n : ℤ} : (m : IGame) ≤ n ↔ m ≤ n := by
  simp [← Game.mk_le_mk]

@[simp]
theorem intCast_lt {m n : ℤ} : (m : IGame) < n ↔ m < n := by
  simp [← Game.mk_lt_mk]

theorem intCast_strictMono : StrictMono ((↑) : ℤ → IGame) :=
  fun _ _ h ↦ intCast_lt.2 h

@[simp]
theorem intCast_inj {m n : ℤ} : (m : IGame) = n ↔ m = n :=
  intCast_strictMono.injective.eq_iff

end IGame
end
