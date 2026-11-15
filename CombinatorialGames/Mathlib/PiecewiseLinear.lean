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

import Mathlib.Algebra.Order.Field.Basic
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

theorem List.SortedLT.of_cons {α : Type*} [LinearOrder α] {a : α} {l : List α}
    (hl : (a :: l).SortedLT) : l.SortedLT := by
  rw [List.sortedLT_cons] at hl
  exact hl.2

/-! ### Partition a linear order via endpoints -/

namespace LinearOrder
variable {α : Type*} [LinearOrder α]

/-- Given a finset `{a₁ < a₂ < ⋯ < aₙ}`, returns the set of intervals
`{Iio a₁, Ico a₁ a₂, Ico a₂ a₃, ⋯}`. These partition the interval `Iio aₙ`. -/
@[to_dual
/-- Given a finset `{a₁ < a₂ < ⋯ < aₙ}`, returns the set of intervals
`{Ioc a₁ a₂, Ioc a₂ a₃, ⋯, Ioi aₙ}`. These partition the interval `Ioi a₁`. -/]
def endpointPartitionIio (e : Finset α) : Finset (Set α) :=
  e.image fun x ↦ {y | ∀ z ∈ e, z < x ↔ z ≤ y}

/-- Given a finset `{a₁ < a₂ < ⋯ < aₙ}`, returns the set of intervals
`{Iio a₁, Ico a₁ a₂, Ico a₂ a₃, ⋯, Ici aₙ}`. These form a partition of the linear order by
left-closed intervals. -/
@[to_dual endpointPartitionRight
/-- Given a finset `{a₁ < a₂ < ⋯ < aₙ}`, returns the set of intervals
`{Iic a₁, Ioc a₁ a₂, Ioc a₂ a₃, ⋯, Ioi aₙ}`. These form a partition of the linear order by
right-closed intervals. -/]
def endpointPartitionLeft (e : Finset α) : Finset (Set α) :=
  insert {y | ∀ z ∈ e, z ≤ y} (endpointPartitionIio e)

@[to_dual (attr := grind =)]
theorem mem_endpointPartitionIio_iff {e : Finset α} {s : Set α} :
    s ∈ endpointPartitionIio e ↔ ∃ t ∈ e, s = {y | ∀ z ∈ e, z < t ↔ z ≤ y} := by
  simp [endpointPartitionIio, eq_comm]

@[to_dual (attr := grind =) mem_endpointPartitionRight_iff]
theorem mem_endpointPartitionLeft_iff {e : Finset α} {s : Set α} :
    s ∈ endpointPartitionLeft e ↔
      s = {y | ∀ z ∈ e, z ≤ y} ∨ ∃ t ∈ e, s = {y | ∀ z ∈ e, z < t ↔ z ≤ y} := by
  rw [endpointPartitionLeft, Finset.mem_insert, mem_endpointPartitionIio_iff]

@[to_dual (attr := simp)]
theorem endpointPartitionIio_empty : endpointPartitionIio (∅ : Finset α) = ∅ := by
  ext; simp [mem_endpointPartitionIio_iff]

@[to_dual (attr := simp) mem_endpointPartitionRight_empty]
theorem endpointPartitionLeft_empty : endpointPartitionLeft (∅ : Finset α) = {univ} := by
  ext; simp [mem_endpointPartitionLeft_iff]

@[to_dual pairwiseDisjoint_endpointPartitionIoi]
theorem pairwiseDisjoint_endpointPartitionIio (e : Finset α) :
    PairwiseDisjoint (endpointPartitionIio e : Set (Set α)) id := by
  intro; grind

@[to_dual pairwiseDisjoint_endpointPartitionRight]
theorem pairwiseDisjoint_endpointPartitionLeft (e : Finset α) :
    PairwiseDisjoint (endpointPartitionLeft e : Set (Set α)) id := by
  intro; grind

@[to_dual]
theorem biUnion_endpointPartitionIio (e : Finset α) :
    ⋃ s ∈ endpointPartitionIio e, s = {y | ∃ z ∈ e, y < z} := by
  ext x
  simp only [mem_endpointPartitionIio_iff, mem_iUnion₂, ↓existsAndEq, mem_ofPred_eq, and_true,
    exists_prop]
  constructor
  · grind
  · intro ⟨y, hy, hxy⟩
    refine ⟨(e.filter (x < ·)).min' (show _ from ⟨y, ?_⟩), ?_, ?_⟩
    · simpa using ⟨hy, hxy⟩
    · exact mem_of_mem_filter _ (min'_mem ..)
    · simp_rw [lt_min'_iff, mem_filter]
      grind

@[to_dual biUnion_endpointPartitionRight]
theorem biUnion_endpointPartitionLeft (e : Finset α) :
    ⋃ y ∈ endpointPartitionLeft e, y = univ := by
  simp_rw [endpointPartitionLeft, Finset.mem_insert, iUnion_iUnion_eq_or_left,
    biUnion_endpointPartitionIio]
  ext
  grind

@[to_dual]
theorem exists_endpointPartitionIio_mem {e : Finset α} {x : α} :
    (∃ s ∈ endpointPartitionIio e, x ∈ s) ↔ ∃ y ∈ e, x < y := by
  simpa using Set.ext_iff.1 (biUnion_endpointPartitionIio e) x

@[to_dual exists_endpointPartitionRight]
theorem exists_endpointPartitionLeft_mem (e : Finset α) (x : α) :
    ∃ s ∈ endpointPartitionLeft e, x ∈ s := by
  simpa using Set.ext_iff.1 (biUnion_endpointPartitionLeft e) x

@[to_dual]
theorem ordConnected_of_mem_endpointPartitionIio {e : Finset α} {s : Set α}
    (hs : s ∈ endpointPartitionIio e) : s.OrdConnected where
  out' := by grind

@[to_dual ordConnected_of_mem_endpointPartitionRight]
theorem ordConnected_of_mem_endpointPartitionLeft {e : Finset α} {s : Set α}
    (hs : s ∈ endpointPartitionLeft e) : s.OrdConnected where
  out' := by grind

@[to_dual]
theorem le_of_mem_endpointPartitionIio {e : Finset α} {s : Set α} {x y : α}
    (hxe : x ∈ e) (hs : s ∈ endpointPartitionIio e) (hx : x ∈ s) (hy : y ∈ s) : x ≤ y := by
  rw [mem_endpointPartitionIio_iff] at hs
  obtain ⟨z, hz, rfl⟩ := hs
  have := hy x hxe
  simp_all

@[to_dual le_of_mem_endpointPartitionRight]
theorem le_of_mem_endpointPartitionLeft {e : Finset α} {s : Set α} {x y : α}
    (hxe : x ∈ e) (hs : s ∈ endpointPartitionLeft e) (hx : x ∈ s) (hy : y ∈ s) : x ≤ y := by
  rw [endpointPartitionLeft, Finset.mem_insert] at hs
  obtain rfl | hs := hs
  · simp_all
  · exact le_of_mem_endpointPartitionIio hxe hs hx hy

@[to_dual]
theorem lt_of_mem_endpointPartitionIio {e : Finset α} {s t : Set α} {x y : α}
    (hs : s ∈ endpointPartitionIio e) (ht : t ∈ endpointPartitionIio e) (hne : s ≠ t)
    (hx : x ∈ s) (hy : y ∈ t) (hxy : x < y) : ∀ a ∈ s, ∀ b ∈ t, a < b := by
  grind

@[to_dual lt_of_mem_endpointPartitionRight]
theorem lt_of_mem_endpointPartitionLeft {e : Finset α} {s t : Set α} {x y : α}
    (hs : s ∈ endpointPartitionLeft e) (ht : t ∈ endpointPartitionLeft e) (hne : s ≠ t)
    (hx : x ∈ s) (hy : y ∈ t) (hxy : x < y) : ∀ a ∈ s, ∀ b ∈ t, a < b := by
  grind

/-- If `e₁ ⊆ e₂`, then `endpointPartitionLeft e₂` is a refinement of
`endpointPartitioLeft e₁`. -/
@[to_dual exists_subset_endpointPartitionRight_of_subset
/-- If `e₁ ⊆ e₂`, then `endpointPartitionRight e₂` is a refinement of
`endpointPartitionRight e₁`. -/]
theorem exists_subset_endpointPartitionLeft_of_subset {e₁ e₂ : Finset α} (h : e₁ ⊆ e₂) {s : Set α}
    (hs : s ∈ endpointPartitionLeft e₂) : ∃ t ∈ endpointPartitionLeft e₁, s ⊆ t := by
  simp_rw [mem_endpointPartitionLeft_iff] at hs ⊢
  obtain rfl | ⟨x, hx₂, rfl⟩ := hs
  · refine ⟨_, .inl rfl, ?_⟩
    grind
  · by_cases hx₁ : x ∈ e₁
    · refine ⟨_, .inr ⟨x, hx₁, rfl⟩, ?_⟩
      grind
    obtain ⟨t, ht, hx⟩ := exists_endpointPartitionLeft_mem e₁ x
    rw [mem_endpointPartitionLeft_iff] at ht
    refine ⟨t, ht, fun y hy ↦ ?_⟩
    obtain rfl | ⟨z, hz, rfl⟩ := ht
    · intro z hz
      rw [← hy z (h hz)]
      apply (hx z hz).lt_of_ne
      rintro rfl
      contradiction
    · grind

/-- A lemma characterizing refinements where points are added in each existing interval. -/
@[to_dual exists_endpointPartitionRight_inter_of_mem_union_image
/-- A lemma characterizing refinements where points are added in each existing interval. -/]
theorem exists_endpointPartitionLeft_inter_of_mem_union_image {e : Finset α}
    (f : endpointPartitionLeft e → α) (hf : ∀ t, f t ∈ t.1) {s : Set α}
    (hs : s ∈ endpointPartitionLeft (e ∪ (endpointPartitionLeft e).attach.image f)) :
    ∃ t : endpointPartitionLeft e, s = t.1 ∩ Iio (f t) ∨ s = t.1 ∩ Ici (f t) := by
  rw [mem_endpointPartitionLeft_iff] at hs
  obtain rfl | ⟨x, hx, rfl⟩ := hs
  · refine ⟨⟨_, Finset.mem_insert_self ..⟩, .inr ?_⟩
    ext x
    constructor
    · grind
    · dsimp
      grind
  · by_cases Hx : x ∈ e
    · let s : endpointPartitionLeft e := ⟨_, mem_endpointPartitionLeft_iff.2 (.inr ⟨x, Hx, rfl⟩)⟩
      refine ⟨s, ?_⟩
      obtain hx | hx := lt_or_ge x (f s)
      · left; grind
      right
      ext y
      constructor
      · grind
      · intro ⟨hy, hys⟩ z hz
        simp only [Finset.mem_union, Finset.mem_image, mem_attach, true_and, Subtype.exists] at hz
        obtain hz | ⟨t, ht, rfl⟩ := hz
        · exact hy z hz
        · refine ⟨fun htx ↦ hys.trans' ?_, fun hty ↦ hty.trans_lt ?_⟩
          · rw [mem_endpointPartitionLeft_iff] at ht
            obtain rfl | ⟨t, ht, rfl⟩ := ht <;> grind
          · simpa using hy x Hx
    · simp only [Finset.mem_union, Finset.mem_image, mem_attach, true_and, Subtype.exists] at hx
      obtain hxe | ⟨s, hs, rfl⟩ := hx
      · contradiction
      refine ⟨⟨s, hs⟩, .inl ?_⟩
      ext x
      constructor
      · intro hx
        constructor
        · rw [mem_endpointPartitionLeft_iff] at hs
          obtain rfl | ⟨y, hy, rfl⟩ := hs
          · intro z hz
            rw [← hx z (Finset.mem_union_left _ hz)]
            apply ((hf ⟨_, hs⟩) z hz).lt_of_ne
            rintro rfl
            contradiction
          · grind
        · simpa using hx (f ⟨s, hs⟩)
      · intro ⟨hx, hxf⟩ y hy
        simp only [Finset.mem_union, Finset.mem_image, mem_attach, true_and, Subtype.exists] at hy
        obtain hy | ⟨y, hy, rfl⟩ := hy
        · grind
        · refine ⟨fun hf' ↦ le_of_lt ?_, hxf.trans_le'⟩
          apply lt_of_mem_endpointPartitionLeft hy hs _ (hf ⟨y, hy⟩) (hf ⟨s, hs⟩) hf'
            _ (hf ⟨y, hy⟩) x hx
          rintro rfl
          exact hf'.false

end LinearOrder

/-! ### Piecewise linear functions -/

namespace Function

variable {K : Type*} [Field K]

/-- A function is linear on a set if it equals a linear polynomial on that set. -/
def IsLinearOn (f : K → K) (s : Set K) : Prop :=
  ∃ a b, ∀ x ∈ s, f x = a * x + b

namespace IsLinearOn
variable {f g : K → K} {s t : Set K}

protected theorem anti (hst : s ⊆ t) (hf : IsLinearOn f t) : IsLinearOn f s := by
  obtain ⟨a, b, hf⟩ := hf
  exact ⟨a, b, fun x hx ↦ hf x (hst hx)⟩

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

protected theorem add (hf : IsLinearOn f s) (hg : IsLinearOn g s) : IsLinearOn (f + g) s := by
  obtain ⟨a, b, hf⟩ := hf
  obtain ⟨c, d, hg⟩ := hg
  refine ⟨a + c, b + d, ?_⟩
  grind [Pi.add_apply]

protected theorem sub (hf : IsLinearOn f s) (hg : IsLinearOn g s) : IsLinearOn (f - g) s := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

theorem ordConnected_image [LinearOrder K] [IsOrderedRing K]
    (hf : IsLinearOn f s) (hs : s.OrdConnected) : (f '' s).OrdConnected where
  out' := by
    obtain ⟨a, b, hf⟩ := hf
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ z ⟨hxz, hzy⟩
    obtain ha | rfl | ha := lt_trichotomy a 0
    · have H : (z - b) / a ∈ s := by
        apply hs.out hy hx
        rw [mem_Icc, le_div_iff_of_neg ha, div_le_iff_of_neg ha]
        grind
      refine ⟨(z - b) / a, H, ?_⟩
      rw [hf _ H]
      grind
    · refine ⟨x, hx, hxz.antisymm ?_⟩
      simp_all
    · have H : (z - b) / a ∈ s := by
        apply hs.out hx hy
        rw [mem_Icc, le_div_iff₀ ha, div_le_iff₀ ha]
        grind
      refine ⟨(z - b) / a, H, ?_⟩
      rw [hf _ H]
      grind

end IsLinearOn

variable [LinearOrder K]

/-- A left-continuous piecewise linear function is one where there exists a finite set of
endpoints, such that the function is linear on each of the intervals they define. -/
@[to_dual IsPiecewiseRightLinear
/-- A right-continuous piecewise linear function is one where there exists a finite set of
endpoints, such that the function is linear on each of the intervals they define. -/]
def IsPiecewiseLeftLinear (f : K → K) : Prop :=
  ∃ e : Finset K, ∀ s ∈ LinearOrder.endpointPartitionLeft e, IsLinearOn f s

namespace IsPiecewiseLeftLinear
variable {f g : K → K}

open LinearOrder

@[to_dual]
protected theorem const (c : K) : IsPiecewiseLeftLinear (const K c) :=
  ⟨∅, by simp⟩

@[to_dual]
protected theorem smul (x : K) (hf : IsPiecewiseLeftLinear f) : IsPiecewiseLeftLinear (x • f) := by
  obtain ⟨s, hs⟩ := hf
  exact ⟨s, fun p hp ↦ (hs p hp).smul x⟩

@[to_dual]
protected theorem qsmul (q : ℚ) (hf : IsPiecewiseLeftLinear f) : IsPiecewiseLeftLinear (q • f) := by
  obtain ⟨s, hs⟩ := hf
  exact ⟨s, fun p hp ↦ (hs p hp).qsmul q⟩

@[to_dual]
protected theorem zsmul (n : ℤ) (hf : IsPiecewiseLeftLinear f) : IsPiecewiseLeftLinear (n • f) := by
  obtain ⟨s, hs⟩ := hf
  exact ⟨s, fun p hp ↦ (hs p hp).zsmul n⟩

@[to_dual]
protected theorem nsmul (n : ℕ) (hf : IsPiecewiseLeftLinear f) : IsPiecewiseLeftLinear (n • f) := by
  obtain ⟨s, hs⟩ := hf
  exact ⟨s, fun p hp ↦ (hs p hp).nsmul n⟩

@[to_dual]
protected theorem neg (hf : IsPiecewiseLeftLinear f) : IsPiecewiseLeftLinear (-f) := by
  obtain ⟨s, hs⟩ := hf
  use s
  simpa

@[to_dual (attr := simp)]
theorem neg_iff : IsPiecewiseLeftLinear (-f) ↔ IsPiecewiseLeftLinear f :=
  ⟨by simpa using IsPiecewiseLeftLinear.neg (f := -f), IsPiecewiseLeftLinear.neg⟩

@[to_dual]
protected theorem add (hf : IsPiecewiseLeftLinear f) (hg : IsPiecewiseLeftLinear g) :
    IsPiecewiseLeftLinear (f + g) := by
  obtain ⟨s, hs⟩ := hf
  obtain ⟨t, ht⟩ := hg
  refine ⟨s ∪ t, fun p hp ↦ ?_⟩
  obtain ⟨q, hq, hpq⟩ :=
    exists_subset_endpointPartitionLeft_of_subset subset_union_left hp
  obtain ⟨r, hr, hpr⟩ :=
    exists_subset_endpointPartitionLeft_of_subset subset_union_right hp
  exact ((hs q hq).anti hpq).add ((ht r hr).anti hpr)

@[to_dual]
protected theorem sub (hf : IsPiecewiseLeftLinear f) (hg : IsPiecewiseLeftLinear g) :
    IsPiecewiseLeftLinear (f - g) := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

private theorem max_zero (hf : IsPiecewiseLeftLinear f) : IsPiecewiseLeftLinear (max f 0) := by
  obtain ⟨s, hs⟩ := hf

  sorry

#exit
protected theorem max (hf : IsPiecewiseLinear f) (hg : IsPiecewiseLinear g) :
    IsPiecewiseLinear (max f g) := by
  rw [← add_zero g, ← add_sub_cancel g f, ← add_sup]
  exact hg.add (hf.sub hg).max_zero

@[to_dual existing]
protected theorem min (hf : IsPiecewiseLinear f) (hg : IsPiecewiseLinear g) :
    IsPiecewiseLinear (min f g) := by
  simpa [← neg_inf] using hf.neg.max hg.neg

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
