/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.SetTheory.Ordinal.Family

/-!
# Declare type aliases of `Ordinal`

This repository contains two type aliases of `Ordinal`, each preserving the order structure but with
distinct arithmetic defined on it, namely `NatOrdinal` and `Nimber`. We define a `ordinal_alias!`
macro which contains all the boilerplate required to set up these types. This also ensures that the
API between both stays consistent.
-/

open Lean

/-- Doc-comment allowing antiquotation. -/
def mkDocComment (s : String) : TSyntax `Lean.Parser.Command.docComment :=
  .mk <| mkNode ``Parser.Command.docComment #[mkAtom "/--", mkAtom (s ++ "-/")]

/-- `Alias.of` -/
def mkOf (Alias : TSyntax `ident) : TSyntax `ident :=
  .mk <| mkIdent (Alias.getId ++ `of)

/-- `Alias.val` -/
def mkVal (Alias : TSyntax `ident) : TSyntax `ident :=
  .mk <| mkIdent (Alias.getId ++ `val)

/-- Declare a type alias of `Ordinal`, preserving the order structure. -/
macro "ordinal_alias!" doc:docComment Alias:ident : command => `(

$doc:docComment
def $Alias : Type _ :=
  Ordinal deriving Zero, One, Nontrivial, Inhabited, WellFoundedRelation

namespace $Alias
universe u

noncomputable instance : LinearOrder $Alias := Ordinal.instLinearOrder
instance : SuccOrder $Alias := Ordinal.instSuccOrder
instance : OrderBot $Alias := Ordinal.instOrderBot
instance : NoMaxOrder $Alias := Ordinal.instNoMaxOrder
instance : ZeroLEOneClass $Alias := Ordinal.instZeroLEOneClass
instance : NeZero (1 : $Alias) := Ordinal.instNeZeroOne
instance : Uncountable $Alias := Ordinal.uncountable
instance : WellFoundedLT $Alias := Ordinal.wellFoundedLT
noncomputable instance : ConditionallyCompleteLinearOrderBot $Alias :=
  Ordinal.instConditionallyCompleteLinearOrderBot

theorem $(mkIdent `lt_wf) : @WellFounded $Alias (· < ·) := Ordinal.lt_wf

$(mkDocComment s!" The identity function between `Ordinal` and `{Alias.getId}`."):docComment
@[match_pattern]
def $(mkIdent `of) : Ordinal ≃o $Alias := .refl _

$(mkDocComment s!" The identity function between `{Alias.getId}` and `Ordinal`."):docComment
@[match_pattern]
def $(mkIdent `val) : $Alias ≃o Ordinal := .refl _

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

@[simp] theorem $(mkIdent `bot_eq_zero) : (⊥ : $Alias) = 0 := rfl

@[simp] theorem $(mkIdent `of_zero) : $(mkOf Alias) 0 = 0 := rfl
@[simp] theorem $(mkIdent `val_zero) : $(mkVal Alias) 0 = 0 := rfl

@[simp] theorem $(mkIdent `of_one) : $(mkOf Alias) 1 = 1 := rfl
@[simp] theorem $(mkIdent `val_one) : $(mkVal Alias) 1 = 1 := rfl

@[simp] theorem $(mkIdent `of_eq_zero) {a} : $(mkOf Alias) a = 0 ↔ a = 0 := .rfl
@[simp] theorem $(mkIdent `val_eq_zero) {a} : $(mkVal Alias) a = 0 ↔ a = 0 := .rfl

@[simp] theorem $(mkIdent `of_eq_one) {a} : $(mkOf Alias) a = 1 ↔ a = 1 := .rfl
@[simp] theorem $(mkIdent `val_eq_one) {a} : $(mkVal Alias) a = 1 ↔ a = 1 := .rfl

theorem $(mkIdent `succ_def) (a : $Alias) : Order.succ a = $(mkOf Alias) ($(mkVal Alias) a + 1) :=
  rfl

$(mkDocComment s!" A recursor for `{Alias.getId}`. Use as `induction x`. "):docComment
@[elab_as_elim, cases_eliminator, induction_eliminator]
protected def $(mkIdent `ind) {β : $Alias → Sort*} ($(mkIdent `mk) :
    ∀ a, β ($(mkOf Alias) a)) (a) : β a :=
  $(mkIdent `mk) ($(mkVal Alias) a)

$(mkDocComment s!" `Ordinal.induction` but for `{Alias.getId}`. "):docComment
theorem $(mkIdent `induction) {p : $Alias → Prop} : ∀ i (_ : ∀ j, (∀ k, k < j → p k) → p j), p i :=
  Ordinal.induction

@[simp] protected theorem $(mkIdent `zero_le) (a : $Alias) : 0 ≤ a := Ordinal.zero_le
@[simp] protected theorem $(mkIdent `le_zero) {a : $Alias} : a ≤ 0 ↔ a = 0 := Ordinal.le_zero
@[simp] protected theorem $(mkIdent `not_lt_zero) (a : $Alias) : ¬ a < 0 := Ordinal.not_lt_zero a
protected theorem $(mkIdent `pos_iff_ne_zero) {a : $Alias} : 0 < a ↔ a ≠ 0 := Ordinal.pos_iff_ne_zero

@[simp] theorem $(mkIdent `lt_one_iff_zero) {a : $Alias} : a < 1 ↔ a = 0 := Ordinal.lt_one_iff_zero
@[simp] theorem $(mkIdent `one_le_iff_ne_zero) {a : $Alias} : 1 ≤ a ↔ a ≠ 0 := Ordinal.one_le_iff_ne_zero
theorem $(mkIdent `le_one_iff) {a : $Alias} : a ≤ 1 ↔ a = 0 ∨ a = 1 := Ordinal.le_one_iff

-- TODO: upstream to Mathlib for Ordinal
theorem $(mkIdent `eq_natCast_of_le_natCast) {a : $Alias} {b : ℕ} (h : a ≤ $(mkOf Alias) b) :
    ∃ c : ℕ, a = $(mkOf Alias) c :=
  Ordinal.lt_omega0.1 (h.trans_lt (Ordinal.nat_lt_omega0 b))

instance (a : $Alias.{u}) : Small.{u} (Set.Iio a) := Ordinal.small_Iio a
instance (a : $Alias.{u}) : Small.{u} (Set.Iic a) := Ordinal.small_Iic a
instance (a b : $Alias.{u}) : Small.{u} (Set.Ico a b) := Ordinal.small_Ico a b
instance (a b : $Alias.{u}) : Small.{u} (Set.Icc a b) := Ordinal.small_Icc a b
instance (a b : $Alias.{u}) : Small.{u} (Set.Ioo a b) := Ordinal.small_Ioo a b
instance (a b : $Alias.{u}) : Small.{u} (Set.Ioc a b) := Ordinal.small_Ioc a b

theorem $(mkIdent `not_bddAbove_compl_of_small) (s : Set $Alias.{u}) [Small.{u} s] : ¬ BddAbove sᶜ :=
  Ordinal.not_bddAbove_compl_of_small s

end $Alias

-- TODO: how do we name this correctly?
-- theorem not_small_nimber : ¬ Small.{u} $Alias.{max u v} := not_small_ordinal
)
