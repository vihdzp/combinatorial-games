/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Partition.Finpartition

import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.Group.Lattice
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Order.Interval.Set.Disjoint

/-!
# Piecewise linear functions
-/

public noncomputable section

open Finset Set

@[to_additive]
instance {R S : Type*} [CommMonoid S] [Preorder S] [IsOrderedMonoid S] :
    IsOrderedMonoid (R → S) where
  mul_le_mul_left _ _ h _ := fun i ↦ mul_le_mul_left (h i) _

/-! ### Partition a linear order via endpoints -/

namespace Finpartition

variable {α : Type*} [LinearOrder α]

private def ofEndpointsPartsAux : List α → Finset (Set α)
  | [] => {}
  | [a] => {Ioi a}
  | a :: b :: l => insert (Ioc a b) (ofEndpointsPartsAux (b :: l))

private theorem Ioi_subset_sup_ofEndpointsPartsAux_cons (a : α) (l : List α) :
    Ioi a ⊆ (ofEndpointsPartsAux (a :: l)).sup id := by
  induction l generalizing a with
  | nil => simp [ofEndpointsPartsAux]
  | cons b l IH =>
    rw [ofEndpointsPartsAux, sup_insert, id]
    grw [← IH, Ioi_subset_Ioc_union_Ioi]

private theorem sup_ofEndpointsPartsAux_cons {a : α} {l : List α} (hl : (a :: l).SortedLE) :
    (ofEndpointsPartsAux (a :: l)).sup id = Ioi a := by
  induction l generalizing a with
  | nil => simp [ofEndpointsPartsAux]
  | cons b l IH =>
    apply (Ioi_subset_sup_ofEndpointsPartsAux_cons a _).antisymm'
    rw [List.sortedLE_cons] at hl
    have hab : a ≤ b := hl.1 _ List.mem_cons_self
    rw [ofEndpointsPartsAux, sup_insert, id, IH hl.2, Ioc_union_Ioi]
    · apply Ioi_subset_Ioi
      simpa
    · simp

private theorem pairwiseDisjoint_ofEndpointsPartsAux {l : List α} (hl : l.SortedLE) :
    PairwiseDisjoint (ofEndpointsPartsAux l : Set (Set α)) id := by
  cases l with
  | nil => simp [ofEndpointsPartsAux]
  | cons a l =>
    induction l generalizing a with
    | nil => simp [ofEndpointsPartsAux]
    | cons b l IH =>
      rw [ofEndpointsPartsAux, coe_insert, pairwiseDisjoint_insert]
      rw [List.sortedLE_cons] at hl
      refine ⟨IH _ hl.2, fun s hs _ ↦ ?_⟩
      apply Set.disjoint_of_subset_right _ (Ioc_disjoint_Ioi le_rfl)
      rw [← sup_ofEndpointsPartsAux_cons hl.2]
      exact le_sup hs

private theorem empty_notMem_ofEndpointsPartsAux [NoMaxOrder α] :
    ∀ {l : List α} (_ : l.SortedLT), ∅ ∉ ofEndpointsPartsAux l
  | [] => by simp [ofEndpointsPartsAux]
  | [a] => by simp [ofEndpointsPartsAux, ← nonempty_iff_empty_ne]
  | a :: b :: l => by
    rw [List.sortedLT_cons]
    intro ⟨hl₁, hl₂⟩
    rw [ofEndpointsPartsAux, Finset.mem_insert, not_or]
    refine ⟨?_, empty_notMem_ofEndpointsPartsAux hl₂⟩
    rw [← ne_eq, ← nonempty_iff_empty_ne, nonempty_Ioc]
    exact hl₁ _ List.mem_cons_self

/-- Given a list `[a₁, a₂, ⋯, aₙ]` returns the finset `{Iic a₁, Ioc a₁ a₂, ⋯, Ioi aₙ}`. -/
def ofEndpointsParts : List α → Finset (Set α)
  | [] => {univ}
  | a :: l => insert (Iic a) (ofEndpointsPartsAux (a :: l))

@[simp]
theorem ofEndpointsParts_nil : ofEndpointsParts [] = {(univ : Set α)} :=
  (rfl)

theorem nonempty_ofEndpointsParts (l : List α) : (ofEndpointsParts l).Nonempty := by
  cases l with
  | nil => simp
  | cons => exact insert_nonempty _ _

theorem sup_ofEndpointsParts (l : List α) : (ofEndpointsParts l).sup id = univ := by
  cases l with
  | nil => simp
  | cons a l =>
    rw [ofEndpointsParts, sup_insert, id]
    grw [← Ioi_subset_sup_ofEndpointsPartsAux_cons, Iic_union_Ioi]

theorem pairwiseDisjoint_ofEndpointsParts {l : List α} (hl : l.SortedLE) :
    PairwiseDisjoint (ofEndpointsParts l : Set (Set α)) id := by
  cases l with
  | nil => simp
  | cons a l =>
    rw [ofEndpointsParts, coe_insert, pairwiseDisjoint_insert]
    refine ⟨pairwiseDisjoint_ofEndpointsPartsAux hl, fun s hs _ ↦ ?_⟩
    apply Set.disjoint_of_subset_right _ (Iic_disjoint_Ioi le_rfl)
    rw [← sup_ofEndpointsPartsAux_cons hl]
    exact le_sup hs

theorem empty_notMem_ofEndpointsParts [Nonempty α] [NoMaxOrder α] {l : List α} (hl : l.SortedLT) :
    ∅ ∉ ofEndpointsParts l := by
  cases l with
  | nil =>
    rw [ofEndpointsParts_nil, notMem_singleton, ne_comm, ← Set.nonempty_iff_ne_empty]
    exact Set.univ_nonempty
  | cons a l =>
    rw [ofEndpointsParts, Finset.mem_insert, not_or, ← ne_eq, ← Set.nonempty_iff_empty_ne]
    exact ⟨nonempty_Iic, empty_notMem_ofEndpointsPartsAux hl⟩

/-- Partition a linear order into intervals `Iic`, `Ioc`, and `Ioi` using a finset of endpoints. -/
def ofEndpoints (s : Finset α) : Finpartition (.univ : Set α) where
  parts := (ofEndpointsParts (s.sort (· ≤ ·))).erase ∅
  supIndep :=
    (pairwiseDisjoint_ofEndpointsParts (sortedLT_sort _).sortedLE).supIndep.subset (erase_subset ..)
  sup_parts := by rw [← Set.bot_eq_empty, sup_erase_bot, sup_ofEndpointsParts]
  bot_notMem := notMem_erase _ _

theorem parts_ofEndpoints (s : Finset α) :
    (ofEndpoints s).parts = (ofEndpointsParts (s.sort (· ≤ ·))).erase ∅ :=
  (rfl)

@[simp]
theorem ofEndpoints_empty [Nonempty α] : ofEndpoints (α := α) ∅ = indiscrete (by simp) := by
  ext; simp +contextual [parts_ofEndpoints]

end Finpartition

/-! ### Piecewise linear functions -/

namespace Function

variable {K : Type*} [Field K]

/-- A function is linear on a set if it equals a linear polynomial on that set. -/
def IsLinearOn (f : K → K) (s : Set K) : Prop :=
  ∃ a b, ∀ t ∈ s, f t = a * t + b

namespace IsLinearOn
variable {f : K → K} {s : Set K}

@[simp]
protected theorem const (c : K) (s : Set K) : IsLinearOn (const K c) s :=
  ⟨0, c, by simp⟩

@[simp]
protected theorem zero (s : Set K) : IsLinearOn 0 s :=
  .const 0 s

@[simp]
protected theorem one (s : Set K) : IsLinearOn 1 s :=
  .const 1 s

protected theorem smul (x : K) (hf : IsLinearOn f s) : IsLinearOn (x • f) s := by
  obtain ⟨a, b, hf⟩ := hf
  refine ⟨x * a, x * b, fun t ht ↦ ?_⟩
  simp [hf t ht, mul_add, mul_assoc]

protected theorem qsmul (q : ℚ) (hf : IsLinearOn f s) : IsLinearOn (q • f) s := by
  convert hf.smul (q : K)
  ext
  simp [Rat.smul_def]

protected theorem zsmul (n : ℤ) (hf : IsLinearOn f s) : IsLinearOn (n • f) s := by
  convert hf.smul (n : K)
  ext
  simp

protected theorem nsmul (n : ℕ) (hf : IsLinearOn f s) : IsLinearOn (n • f) s := by
  convert hf.smul (n : K)
  ext
  simp

protected theorem neg (hf : IsLinearOn f s) : IsLinearOn (-f) s := by
  simpa using hf.zsmul (-1)

@[simp]
theorem neg_iff : IsLinearOn (-f) s ↔ IsLinearOn f s :=
  ⟨by simpa using IsLinearOn.neg (f := -f), IsLinearOn.neg⟩

end IsLinearOn

variable [LinearOrder K]

/-- A (left-continuous) piecewise linear function is one where there exists a finite set of
endpoints, such that the function is linear on each of the intervals they define. -/
def IsPiecewiseLinear (f : K → K) : Prop :=
  ∃ e : Finset K, ∀ p ∈ (Finpartition.ofEndpoints e).parts, IsLinearOn f p

namespace IsPiecewiseLinear
variable {f g : K → K}

protected theorem const (c : K) : IsPiecewiseLinear (const K c) :=
  ⟨∅, by simp⟩

protected theorem smul (x : K) (hf : IsPiecewiseLinear f) : IsPiecewiseLinear (x • f) := by
  obtain ⟨s, hs⟩ := hf
  exact ⟨s, fun p hp ↦ (hs p hp).smul x⟩

protected theorem qsmul (q : ℚ) (hf : IsPiecewiseLinear f) : IsPiecewiseLinear (q • f) := by
  obtain ⟨s, hs⟩ := hf
  exact ⟨s, fun p hp ↦ (hs p hp).qsmul q⟩

protected theorem zsmul (n : ℤ) (hf : IsPiecewiseLinear f) : IsPiecewiseLinear (n • f) := by
  obtain ⟨s, hs⟩ := hf
  exact ⟨s, fun p hp ↦ (hs p hp).zsmul n⟩

protected theorem nsmul (n : ℕ) (hf : IsPiecewiseLinear f) : IsPiecewiseLinear (n • f) := by
  obtain ⟨s, hs⟩ := hf
  exact ⟨s, fun p hp ↦ (hs p hp).nsmul n⟩

protected theorem neg (hf : IsPiecewiseLinear f) : IsPiecewiseLinear (-f) := by
  obtain ⟨s, hs⟩ := hf
  use s
  simpa

@[simp]
theorem neg_iff : IsPiecewiseLinear (-f) ↔ IsPiecewiseLinear f :=
  ⟨by simpa using IsPiecewiseLinear.neg (f := -f), IsPiecewiseLinear.neg⟩

variable [IsOrderedRing K]

protected theorem add (hf : IsPiecewiseLinear f) (hg : IsPiecewiseLinear g) :
    IsPiecewiseLinear (f + g) :=
  sorry

protected theorem sub (hf : IsPiecewiseLinear f) (hg : IsPiecewiseLinear g) :
    IsPiecewiseLinear (f - g) := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

@[to_dual]
protected theorem max (hf : IsPiecewiseLinear f) (hg : IsPiecewiseLinear g) :
    IsPiecewiseLinear (max f g) :=
  sorry

end IsPiecewiseLinear

variable (K) in
/-- The subtype of piecewise linear functions. -/
abbrev PiecewiseLinear : Type _ := Subtype (IsPiecewiseLinear (K := K))

namespace PiecewiseLinear

instance : CoeFun (PiecewiseLinear K) (fun _ ↦ K → K) where
  coe := Subtype.val

theorem isPiecewiseLinear (f : PiecewiseLinear K) : IsPiecewiseLinear f :=
  f.2

@[ext]
theorem ext {f g : PiecewiseLinear K} (H : ∀ x, f x = g x) : f = g :=
  Subtype.ext (funext H)

/-- The constant function as a piecewise linear function. -/
@[expose]
protected def const (c : K) : PiecewiseLinear K :=
  ⟨_, .const c⟩

instance : Zero (PiecewiseLinear K) := ⟨.const 0⟩
instance : One (PiecewiseLinear K) := ⟨.const 1⟩

@[simp] theorem coe_zero : (0 : PiecewiseLinear K) = (0 : K → K) := rfl
@[simp] theorem coe_one : (1 : PiecewiseLinear K) = (1 : K → K) := rfl

instance : SMul K (PiecewiseLinear K) where
  smul x f := ⟨_, f.2.smul x⟩

instance : ZSMul (PiecewiseLinear K) where
  zsmul n f := ⟨_, f.2.zsmul n⟩

instance : NSMul (PiecewiseLinear K) where
  nsmul n f := ⟨_, f.2.nsmul n⟩

@[simp]
theorem coe_smul (x : K) (f : PiecewiseLinear K) : (x • f : PiecewiseLinear K) = (x • f : K → K) :=
  rfl

@[simp]
theorem coe_zsmul (n : ℤ) (f : PiecewiseLinear K) : (n • f : PiecewiseLinear K) = (n • f : K → K) :=
  rfl

@[simp]
theorem coe_nsmul (n : ℕ) (f : PiecewiseLinear K) : (n • f : PiecewiseLinear K) = (n • f : K → K) :=
  rfl

variable [IsOrderedRing K]

instance : Add (PiecewiseLinear K) where
  add f g := ⟨_, f.2.add g.2⟩

@[simp]
theorem coe_add (f g : PiecewiseLinear K) : (f + g : PiecewiseLinear K) = (f + g : K → K) :=
  rfl

instance : AddCommMonoidWithOne (PiecewiseLinear K) where
  zero_add f := by ext; exact zero_add ..
  add_zero f := by ext; exact add_zero ..
  add_comm f g := by ext; exact add_comm ..
  add_assoc f g h := by ext; exact add_assoc ..
  nsmul_zero f := by ext; simp
  nsmul_succ f n := by ext; simp [add_one_mul]

@[to_dual]
instance : Max (PiecewiseLinear K) where
  max f g := ⟨_, f.2.max g.2⟩

@[to_dual (attr := simp)]
theorem coe_sup (f g : PiecewiseLinear K) : (f ⊔ g : PiecewiseLinear K) = (f ⊔ g : K → K) :=
  rfl

@[to_dual]
instance : SemilatticeSup (PiecewiseLinear K) where
  sup f g := max f g
  le_sup_left _ _ _  := le_sup_left
  le_sup_right _ _ _  := le_sup_right
  sup_le _f _g _h hfg hgh x := sup_le (hfg x) (hgh x)

instance : Lattice (PiecewiseLinear K) where

end PiecewiseLinear
end Function
