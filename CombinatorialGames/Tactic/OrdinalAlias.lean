/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Data.Nat.Lattice
public import Mathlib.SetTheory.Ordinal.Family

/-!
# Declare type aliases of `Ordinal`

This repository contains two type aliases of `Ordinal`, each preserving the order structure but with
distinct arithmetic defined on it, namely `NatOrdinal` and `Nimber`. We define a `ordinal_alias!`
macro which contains all the boilerplate required to set up these types. This also ensures that the
API between both stays consistent.
-/

open Lean

/-! ### For Mathlib -/

public section

namespace Ordinal

theorem eq_natCast_of_le_natCast {a : Ordinal} {b : ℕ} (h : a ≤ b) : ∃ c : ℕ, a = c :=
  Ordinal.lt_omega0.1 (h.trans_lt (Ordinal.nat_lt_omega0 b))

theorem Iio_zero : Set.Iio (0 : Ordinal) = ∅ := by simp
@[simp] theorem Iio_one : Set.Iio (1 : Ordinal) = {0} := by
  rw [← succ_zero, Order.Iio_succ]; exact Set.Iic_bot
@[simp] theorem Iio_two : Set.Iio (2 : Ordinal) = {0, 1} := by
  rw [← succ_one, Order.Iio_succ]; ext; simp [le_one_iff]

end Ordinal
end

/-! ### Auxiliary defs -/

/-- Doc-comment allowing antiquotation. -/
meta def mkDocComment (s : String) : TSyntax `Lean.Parser.Command.docComment :=
  .mk <| mkNode ``Parser.Command.docComment #[mkAtom "/--", mkAtom (s ++ "-/")]

/-- `Alias.of` -/
meta def mkOf (Alias : TSyntax `ident) : TSyntax `ident :=
  .mk <| mkIdent (Alias.getId ++ `of)

/-- `Alias.val` -/
meta def mkVal (Alias : TSyntax `ident) : TSyntax `ident :=
  .mk <| mkIdent (Alias.getId ++ `val)

/-! ### Macros -/

/-- Declare a type alias of either `Ordinal` or `Nat`, preserving the order structure. -/
macro "alias!" doc:docComment Alias:ident Source:ident : command => `(
@[expose] public section

$doc:docComment
def $Alias : Type _ :=
  $Source deriving Zero, One, Nontrivial, Inhabited, WellFoundedRelation

namespace $Alias
universe u

instance : PartialOrder $Alias := inferInstanceAs (PartialOrder $Source)
instance : SuccOrder $Alias := inferInstanceAs (SuccOrder $Source)
instance : OrderBot $Alias := inferInstanceAs (OrderBot $Source)
instance : NoMaxOrder $Alias := inferInstanceAs (NoMaxOrder $Source)
instance : ZeroLEOneClass $Alias := inferInstanceAs (ZeroLEOneClass $Source)
instance : NeZero (1 : $Alias) := inferInstanceAs (NeZero (1 : $Source))
instance : WellFoundedLT $Alias := inferInstanceAs (WellFoundedLT $Source)
noncomputable instance : ConditionallyCompleteLinearOrderBot $Alias :=
  inferInstanceAs (ConditionallyCompleteLinearOrderBot $Source)

theorem $(mkIdent `lt_wf) : @WellFounded $Alias (· < ·) := wellFounded_lt

$(mkDocComment s!" The identity function between `{Source.getId}` and `{Alias.getId}`."):docComment
@[match_pattern]
def $(mkIdent `of) : $Source ≃o $Alias := .refl _

$(mkDocComment s!" The identity function between `{Alias.getId}` and `{Source.getId}`."):docComment
@[match_pattern]
def $(mkIdent `val) : $Alias ≃o $Source := .refl _

@[simp] theorem $(mkIdent `of_symm) : .symm $(mkOf Alias) = $(mkVal Alias) := rfl
@[simp] theorem $(mkIdent `val_symm) : .symm $(mkVal Alias) = $(mkOf Alias) := rfl

@[simp] theorem $(mkIdent `of_val) (a) : $(mkOf Alias) ($(mkVal Alias) a) = a := rfl
@[simp] theorem $(mkIdent `val_of) (a) : $(mkVal Alias) ($(mkOf Alias) a) = a := rfl

theorem $(mkIdent `val_le_iff) {a b} : $(mkVal Alias) a ≤ b ↔ a ≤ $(mkOf Alias) b := .rfl
theorem $(mkIdent `val_lt_iff) {a b} : $(mkVal Alias) a < b ↔ a < $(mkOf Alias) b := .rfl
theorem $(mkIdent `val_eq_iff) {a b} : $(mkVal Alias) a = b ↔ a = $(mkOf Alias) b := .rfl

theorem $(mkIdent `of_le_iff) {a b} : $(mkOf Alias) a ≤ b ↔ a ≤ $(mkVal Alias) b := .rfl
theorem $(mkIdent `of_lt_iff) {a b} : $(mkOf Alias) a < b ↔ a < $(mkVal Alias) b := .rfl
theorem $(mkIdent `of_eq_iff) {a b} : $(mkOf Alias) a = b ↔ a = $(mkVal Alias) b := .rfl

@[simp]
theorem $(mkIdent `of_image_Iio) (a) : $(mkOf Alias) '' Set.Iio a = Set.Iio ($(mkOf Alias) a) :=
  Set.image_id _

@[simp]
theorem $(mkIdent `val_image_Iio) (a) : $(mkVal Alias) '' Set.Iio a = Set.Iio ($(mkVal Alias) a) :=
  Set.image_id _

@[simp] theorem $(mkIdent `bot_eq_zero) : (⊥ : $Alias) = 0 := rfl

@[simp] theorem $(mkIdent `of_zero) : $(mkOf Alias) 0 = 0 := rfl
@[simp] theorem $(mkIdent `val_zero) : $(mkVal Alias) 0 = 0 := rfl

@[simp] theorem $(mkIdent `of_one) : $(mkOf Alias) 1 = 1 := rfl
@[simp] theorem $(mkIdent `val_one) : $(mkVal Alias) 1 = 1 := rfl

@[simp] theorem $(mkIdent `of_eq_zero) {a} : $(mkOf Alias) a = 0 ↔ a = 0 := .rfl
@[simp] theorem $(mkIdent `val_eq_zero) {a} : $(mkVal Alias) a = 0 ↔ a = 0 := .rfl

@[simp] theorem $(mkIdent `of_eq_one) {a} : $(mkOf Alias) a = 1 ↔ a = 1 := .rfl
@[simp] theorem $(mkIdent `val_eq_one) {a} : $(mkVal Alias) a = 1 ↔ a = 1 := .rfl
@[simp] theorem $(mkIdent `of_le_one) {a} : $(mkOf Alias) a ≤ 1 ↔ a ≤ 1 := .rfl
@[simp] theorem $(mkIdent `val_le_one) {a} : $(mkVal Alias) a ≤ 1 ↔ a ≤ 1 := .rfl
@[simp] theorem $(mkIdent `one_le_of) {a} : 1 ≤ $(mkOf Alias) a ↔ 1 ≤ a := .rfl
@[simp] theorem $(mkIdent `one_le_val) {a} : 1 ≤ $(mkVal Alias) a ↔ 1 ≤ a := .rfl
@[simp] theorem $(mkIdent `of_lt_one) {a} : $(mkOf Alias) a < 1 ↔ a < 1 := .rfl
@[simp] theorem $(mkIdent `val_lt_one) {a} : $(mkVal Alias) a < 1 ↔ a < 1 := .rfl
@[simp] theorem $(mkIdent `one_lt_of) {a} : 1 < $(mkOf Alias) a ↔ 1 < a := .rfl
@[simp] theorem $(mkIdent `one_lt_val) {a} : 1 < $(mkVal Alias) a ↔ 1 < a := .rfl

theorem $(mkIdent `succ_def) (a : $Alias) : Order.succ a = $(mkOf Alias) ($(mkVal Alias) a + 1) :=
  rfl

@[simp]
theorem $(mkIdent `succ_of) (a : $Source) : Order.succ ($(mkOf Alias) a) = $(mkOf Alias) (a + 1) :=
  rfl

@[simp] theorem $(mkIdent `succ_ne_zero) (a : $Alias) : Order.succ a ≠ 0 := Order.succ_ne_bot a

$(mkDocComment s!" A recursor for `{Alias.getId}`. Use as `induction x`. "):docComment
@[elab_as_elim, cases_eliminator, induction_eliminator]
protected def $(mkIdent `ind) {motive : $Alias → Sort*}
    ($(mkIdent `mk) : ∀ a, motive ($(mkOf Alias) a)) (a) : motive a :=
  $(mkIdent `mk) ($(mkVal Alias) a)

$(mkDocComment s!" Well-founded induction for `{Alias.getId}`. "):docComment
theorem $(mkIdent `induction) {p : $Alias → Prop} : ∀ i (_ : ∀ j, (∀ k, k < j → p k) → p j), p i :=
  WellFoundedLT.induction

@[simp] theorem $(mkIdent `zero_le) (a : $Alias) : 0 ≤ a := bot_le
@[simp] theorem $(mkIdent `le_zero) {a : $Alias} : a ≤ 0 ↔ a = 0 := le_bot_iff
@[simp] theorem $(mkIdent `not_neg) (a : $Alias) : ¬ a < 0 := not_lt_bot
protected theorem $(mkIdent `pos_iff_ne_zero) {a : $Alias} : 0 < a ↔ a ≠ 0 := bot_lt_iff_ne_bot
protected theorem $(mkIdent `eq_zero_or_pos) (a : $Alias) : a = 0 ∨ 0 < a := eq_bot_or_bot_lt a

end $Alias
end
)

/-- Declare a type alias of `Ordinal`, preserving the order structure. -/
macro "ordinal_alias!" doc:docComment Alias:ident : command => `(

alias! $doc $Alias Ordinal

@[expose] public section
namespace $Alias
universe u

noncomputable instance : LinearOrder $Alias := Ordinal.instLinearOrder
instance : Uncountable $Alias := Ordinal.uncountable

@[simp] theorem $(mkIdent `lt_one_iff_zero) {a : $Alias} : a < 1 ↔ a = 0 := Ordinal.lt_one_iff_zero
theorem $(mkIdent `le_one_iff) {a : $Alias} : a ≤ 1 ↔ a = 0 ∨ a = 1 := Ordinal.le_one_iff

@[simp]
theorem $(mkIdent `one_le_iff_ne_zero) {a : $Alias} : 1 ≤ a ↔ a ≠ 0 :=
  Ordinal.one_le_iff_ne_zero

@[simp] theorem $(mkIdent `succ_zero) : Order.succ (0 : $Alias) = 1 := Ordinal.succ_zero

@[simp] theorem $(mkIdent `Iio_zero) : Set.Iio (0 : $Alias) = ∅ := Ordinal.Iio_zero
@[simp] theorem $(mkIdent `Iio_one) : Set.Iio (1 : $Alias) = {0} := Ordinal.Iio_one

theorem $(mkIdent `eq_natCast_of_le_natCast) {a : $Alias} {b : ℕ} (h : a ≤ $(mkOf Alias) b) :
    ∃ c : ℕ, a = $(mkOf Alias) c :=
  Ordinal.eq_natCast_of_le_natCast h

instance (a : $Alias.{u}) : Small.{u} (Set.Iio a) := Ordinal.small_Iio a
instance (a : $Alias.{u}) : Small.{u} (Set.Iic a) := Ordinal.small_Iic a
instance (a b : $Alias.{u}) : Small.{u} (Set.Ico a b) := Ordinal.small_Ico a b
instance (a b : $Alias.{u}) : Small.{u} (Set.Icc a b) := Ordinal.small_Icc a b
instance (a b : $Alias.{u}) : Small.{u} (Set.Ioo a b) := Ordinal.small_Ioo a b
instance (a b : $Alias.{u}) : Small.{u} (Set.Ioc a b) := Ordinal.small_Ioc a b

instance : IsEmpty (Set.Iio (0 : $Alias)) := Ordinal.instIsEmptyIioZero
instance : Unique (Set.Iio (1 : $Alias)) := Ordinal.uniqueIioOne

@[simp]
theorem $(mkIdent `Iio_one_default_eq) :
    (default : Set.Iio (1 : $Alias)) = ⟨0, zero_lt_one' $Alias⟩ :=
  rfl

theorem $(mkIdent `bddAbove_iff_small) {s : Set $Alias.{u}} : BddAbove s ↔ Small.{u} s :=
  Ordinal.bddAbove_iff_small

theorem $(mkIdent `bddAbove_of_small) (s : Set $Alias.{u}) [Small.{u} s] : BddAbove s :=
  Ordinal.bddAbove_of_small s

theorem $(mkIdent `not_bddAbove_compl_of_small) (s : Set $Alias.{u}) [Small.{u} s] : ¬BddAbove sᶜ :=
  Ordinal.not_bddAbove_compl_of_small s

theorem $(mkIdent `le_iSup) {ι : Type*} (f : ι → $Alias.{u}) [Small.{u} ι] (i : ι) : f i ≤ iSup f :=
  Ordinal.le_iSup f i

theorem $(mkIdent `iSup_le_iff) {ι : Type*} {f : ι → $Alias.{u}} {a : $Alias.{u}} [Small.{u} ι] :
    ⨆ i, f i ≤ a ↔ ∀ i, f i ≤ a :=
  Ordinal.iSup_le_iff

theorem $(mkIdent `lt_iSup_iff) {ι : Type*} [Small.{u} ι] (f : ι → $Alias.{u}) {x} :
    x < ⨆ i, f i ↔ ∃ i, x < f i :=
  Ordinal.lt_iSup_iff

theorem $(mkIdent `iSup_eq_zero_iff) {ι : Type*} [Small.{u} ι] {f : ι → $Alias.{u}} :
    ⨆ i, f i = 0 ↔ ∀ i, f i = 0 :=
  Ordinal.iSup_eq_zero_iff

end $Alias
end

-- TODO: how do we name this correctly?
-- theorem not_small_nimber : ¬ Small.{u} $Alias.{max u v} := not_small_ordinal
)
