import Mathlib.SetTheory.Ordinal.Family

open Lean Elab Command

-- $(mkDocComment s!" Docstring for {decl.getId} docstring {"hello"}"):docComment

def mkDocComment (s : String) : TSyntax `Lean.Parser.Command.docComment :=
  .mk <| mkNode ``Parser.Command.docComment #[mkAtom "/--", mkAtom (s ++ "-/")]

macro "ordinal_alias!" doc:docComment x:ident : command => `(

$doc:docComment
def $x : Type _ :=
  Ordinal deriving Zero, Inhabited, One, WellFoundedRelation

instance : LinearOrder $x := Ordinal.instLinearOrder
instance : SuccOrder $x := Ordinal.instSuccOrder
instance : OrderBot $x := Ordinal.instOrderBot
instance : NoMaxOrder $x := Ordinal.instNoMaxOrder
instance : ZeroLEOneClass $x := Ordinal.instZeroLEOneClass
instance : NeZero (1 : $x) := Ordinal.instNeZeroOne
instance : Uncountable $x := Ordinal.uncountable

$(mkDocComment s!" The identity function between `Ordinal` and `{x.getId}`."):docComment
@[match_pattern]
def Ordinal.toNatOrdinal : Ordinal ≃o $x := .refl _

$(mkDocComment s!" The identity function between `{x.getId}` and `Ordinal`."):docComment
@[match_pattern]
def $(mkIdent (x.getId ++ `toOrdinal)) : $x ≃o Ordinal := .refl _
/-
namespace NatOrdinal

open Ordinal

@[simp] theorem toOrdinal_symm : toOrdinal.symm = Ordinal.toNatOrdinal := rfl

@[simp]
theorem toOrdinal_toNatOrdinal (a : NatOrdinal) : a.toOrdinal.toNatOrdinal = a :=
  rfl

theorem lt_wf : @WellFounded NatOrdinal (· < ·) :=
  Ordinal.lt_wf

instance : WellFoundedLT NatOrdinal :=
  Ordinal.wellFoundedLT

instance : ConditionallyCompleteLinearOrderBot NatOrdinal :=
  WellFoundedLT.conditionallyCompleteLinearOrderBot _

instance (o : NatOrdinal.{u}) : Small.{u} (Iio o) :=
  inferInstanceAs (Small (Iio o.toOrdinal))

theorem bddAbove_of_small (s : Set NatOrdinal.{u}) [Small.{u} s] : BddAbove s :=
  Ordinal.bddAbove_of_small s

@[simp]
theorem bot_eq_zero : ⊥ = 0 :=
  rfl

@[simp]
theorem toOrdinal_zero : toOrdinal 0 = 0 :=
  rfl

@[simp]
theorem toOrdinal_one : toOrdinal 1 = 1 :=
  rfl

@[simp]
theorem toOrdinal_eq_zero {a} : toOrdinal a = 0 ↔ a = 0 :=
  Iff.rfl

@[simp]
theorem toOrdinal_eq_one {a} : toOrdinal a = 1 ↔ a = 1 :=
  Iff.rfl

theorem toOrdinal_max (a b : NatOrdinal) : toOrdinal (max a b) = max (toOrdinal a) (toOrdinal b) :=
  rfl

theorem toOrdinal_min (a b : NatOrdinal) : toOrdinal (min a b) = min (toOrdinal a) (toOrdinal b) :=
  rfl

theorem succ_def (a : NatOrdinal) : succ a = toNatOrdinal (toOrdinal a + 1) :=
  rfl

@[simp]
theorem zero_le (o : NatOrdinal) : 0 ≤ o :=
  Ordinal.zero_le o

theorem not_lt_zero (o : NatOrdinal) : ¬ o < 0 :=
  Ordinal.not_lt_zero o

@[simp]
theorem lt_one_iff_zero {o : NatOrdinal} : o < 1 ↔ o = 0 :=
  Ordinal.lt_one_iff_zero

/-- A recursor for `NatOrdinal`. Use as `induction x`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
protected def rec {β : NatOrdinal → Sort*} (h : ∀ a, β (toNatOrdinal a)) : ∀ a, β a := fun a =>
  h (toOrdinal a)

/-- `Ordinal.induction` but for `NatOrdinal`. -/
theorem induction {p : NatOrdinal → Prop} : ∀ (i) (_ : ∀ j, (∀ k, k < j → p k) → p j), p i :=
  Ordinal.induction

end NatOrdinal

namespace Ordinal

variable {a b c : Ordinal.{u}}

@[simp]
theorem toNatOrdinal_symm_eq : toNatOrdinal.symm = NatOrdinal.toOrdinal :=
  rfl

@[simp]
theorem toNatOrdinal_toOrdinal (a : Ordinal) : a.toNatOrdinal.toOrdinal = a :=
  rfl

@[simp]
theorem toNatOrdinal_zero : toNatOrdinal 0 = 0 :=
  rfl

@[simp]
theorem toNatOrdinal_one : toNatOrdinal 1 = 1 :=
  rfl

@[simp]
theorem toNatOrdinal_eq_zero (a) : toNatOrdinal a = 0 ↔ a = 0 :=
  Iff.rfl

@[simp]
theorem toNatOrdinal_eq_one (a) : toNatOrdinal a = 1 ↔ a = 1 :=
  Iff.rfl

theorem toNatOrdinal_max (a b : Ordinal) :
    toNatOrdinal (max a b) = max (toNatOrdinal a) (toNatOrdinal b) :=
  rfl

theorem toNatOrdinal_min (a b : Ordinal) :
    toNatOrdinal (min a b) = min (toNatOrdinal a) (toNatOrdinal b) :=
  rfl
  -/

)

noncomputable section
ordinal_alias! /-- A type synonym for ordinals with natural addition and multiplication. -/ NatOrdinal

#synth NatOrdinal.toOrdinal
