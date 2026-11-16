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
public import Mathlib.Data.Finset.DenselyOrdered
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

instance (priority := 100) IsStrictOrderedRing.toNoMinOrder {R : Type*}
    [Ring R] [PartialOrder R] [IsStrictOrderedRing R] : NoMinOrder R :=
  ⟨fun a => ⟨a - 1, by simp⟩⟩

@[to_dual existing IsStrictOrderedRing.toNoMinOrder]
theorem IsStrictOrderedRing.toNoMaxOrder' {R : Type*}
    [Ring R] [PartialOrder R] [IsStrictOrderedRing R] : NoMaxOrder R :=
  inferInstance

attribute [to_dual self (reorder := x y, 6 8)] Set.OrdConnected.out

attribute [to_dual existing] instNoMaxOrderOfNontrivial

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
right-open intervals. -/
@[to_dual endpointPartitionLeft
/-- Given a finset `{a₁ < a₂ < ⋯ < aₙ}`, returns the set of intervals
`{Iic a₁, Ioc a₁ a₂, Ioc a₂ a₃, ⋯, Ioi aₙ}`. These form a partition of the linear order by
left-open intervals. -/]
def endpointPartitionRight (e : Finset α) : Finset (Set α) :=
  insert {y | ∀ z ∈ e, z ≤ y} (endpointPartitionIio e)

@[to_dual (attr := grind =)]
theorem mem_endpointPartitionIio_iff {e : Finset α} {s : Set α} :
    s ∈ endpointPartitionIio e ↔ ∃ t ∈ e, s = {y | ∀ z ∈ e, z < t ↔ z ≤ y} := by
  simp [endpointPartitionIio, eq_comm]

@[to_dual (attr := grind =) mem_endpointPartitionLeft_iff]
theorem mem_endpointPartitionRight_iff {e : Finset α} {s : Set α} :
    s ∈ endpointPartitionRight e ↔
      s = {y | ∀ z ∈ e, z ≤ y} ∨ ∃ t ∈ e, s = {y | ∀ z ∈ e, z < t ↔ z ≤ y} := by
  rw [endpointPartitionRight, Finset.mem_insert, mem_endpointPartitionIio_iff]

@[to_dual (attr := simp)]
theorem endpointPartitionIio_empty : endpointPartitionIio (∅ : Finset α) = ∅ := by
  ext; simp [mem_endpointPartitionIio_iff]

@[to_dual (attr := simp) mem_endpointPartitionLeft_empty]
theorem endpointPartitionRight_empty : endpointPartitionRight (∅ : Finset α) = {univ} := by
  ext; simp [mem_endpointPartitionRight_iff]

@[to_dual pairwiseDisjoint_endpointPartitionIoi]
theorem pairwiseDisjoint_endpointPartitionIio (e : Finset α) :
    PairwiseDisjoint (endpointPartitionIio e : Set (Set α)) id := by
  intro; grind

@[to_dual pairwiseDisjoint_endpointPartitionLeft]
theorem pairwiseDisjoint_endpointPartitionRight (e : Finset α) :
    PairwiseDisjoint (endpointPartitionRight e : Set (Set α)) id := by
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

@[to_dual biUnion_endpointPartitionLeft]
theorem biUnion_endpointPartitionRight (e : Finset α) :
    ⋃ y ∈ endpointPartitionRight e, y = univ := by
  simp_rw [endpointPartitionRight, Finset.mem_insert, iUnion_iUnion_eq_or_left,
    biUnion_endpointPartitionIio]
  ext
  grind

@[to_dual]
theorem exists_endpointPartitionIio_mem {e : Finset α} {x : α} :
    (∃ s ∈ endpointPartitionIio e, x ∈ s) ↔ ∃ y ∈ e, x < y := by
  simpa using Set.ext_iff.1 (biUnion_endpointPartitionIio e) x

@[to_dual exists_endpointPartitionLeft]
theorem exists_endpointPartitionRight_mem (e : Finset α) (x : α) :
    ∃ s ∈ endpointPartitionRight e, x ∈ s := by
  simpa using Set.ext_iff.1 (biUnion_endpointPartitionRight e) x

@[to_dual]
theorem ordConnected_of_mem_endpointPartitionIio {e : Finset α} {s : Set α}
    (hs : s ∈ endpointPartitionIio e) : s.OrdConnected where
  out' := by grind

@[to_dual ordConnected_of_mem_endpointPartitionLeft]
theorem ordConnected_of_mem_endpointPartitionRight {e : Finset α} {s : Set α}
    (hs : s ∈ endpointPartitionRight e) : s.OrdConnected where
  out' := by grind

@[to_dual]
theorem le_of_mem_endpointPartitionIio {e : Finset α} {s : Set α} {x y : α}
    (hxe : x ∈ e) (hs : s ∈ endpointPartitionIio e) (hx : x ∈ s) (hy : y ∈ s) : x ≤ y := by
  rw [mem_endpointPartitionIio_iff] at hs
  obtain ⟨z, hz, rfl⟩ := hs
  have := hy x hxe
  simp_all

@[to_dual le_of_mem_endpointPartitionLeft]
theorem le_of_mem_endpointPartitionRight {e : Finset α} {s : Set α} {x y : α}
    (hxe : x ∈ e) (hs : s ∈ endpointPartitionRight e) (hx : x ∈ s) (hy : y ∈ s) : x ≤ y := by
  rw [endpointPartitionRight, Finset.mem_insert] at hs
  obtain rfl | hs := hs
  · simp_all
  · exact le_of_mem_endpointPartitionIio hxe hs hx hy

@[to_dual]
theorem lt_of_mem_endpointPartitionIio {e : Finset α} {s t : Set α} {x y : α}
    (hs : s ∈ endpointPartitionIio e) (ht : t ∈ endpointPartitionIio e) (hne : s ≠ t)
    (hx : x ∈ s) (hy : y ∈ t) (hxy : x < y) : ∀ a ∈ s, ∀ b ∈ t, a < b := by
  grind

@[to_dual lt_of_mem_endpointPartitionLeft]
theorem lt_of_mem_endpointPartitionRight {e : Finset α} {s t : Set α} {x y : α}
    (hs : s ∈ endpointPartitionRight e) (ht : t ∈ endpointPartitionRight e) (hne : s ≠ t)
    (hx : x ∈ s) (hy : y ∈ t) (hxy : x < y) : ∀ a ∈ s, ∀ b ∈ t, a < b := by
  grind

-- TODO: dualize `Finset.exists_between`
-- TODO: make versions that only assume one of `NoMaxOrder` or `NoMinOrder`
@[to_dual none]
theorem _root_.Finset.exists_between'' [DenselyOrdered α] {s t : Finset α}
    (hs : s.Nonempty) (ht : t.Nonempty) (H : ∀ x ∈ s, ∀ y ∈ t, x < y) :
    ∃ b, (∀ x ∈ s, x < b) ∧ (∀ y ∈ t, b < y) := by
  convert! _root_.exists_between (a₁ := s.max' hs) (a₂ := t.min' ht) (by simp_all) <;> simp

@[to_dual]
theorem nonempty_of_mem_endpointPartitionIio [NoMinOrder α] [DenselyOrdered α]
    {e : Finset α} {s : Set α} (hs : s ∈ endpointPartitionIio e) : s.Nonempty := by
  rw [mem_endpointPartitionIio_iff] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  by_cases! Ht : ∀ x < t, x ∉ e
  · obtain ⟨x, hx⟩ := exists_lt t
    use x
    grind
  · obtain ⟨x, hx, hx'⟩ := Ht
    obtain ⟨y, hy, hy'⟩ := Finset.exists_between'' (s := e.filter (· < t)) (t := {t})
      (by use x; simpa using ⟨hx', hx⟩) (by simp) (by simp)
    use y
    simp_rw [Finset.mem_singleton, forall_eq] at hy'
    simp_rw [mem_filter, and_imp] at hy
    exact fun z hz ↦ ⟨fun hz' ↦ (hy z hz hz').le, hy'.trans_le'⟩

@[to_dual nonempty_of_mem_endpointPartitionLeft]
theorem nonempty_of_mem_endpointPartitionRight [Nonempty α] [NoMinOrder α] [DenselyOrdered α]
    {e : Finset α} {s : Set α} (hs : s ∈ endpointPartitionRight e) : s.Nonempty := by
  rw [endpointPartitionRight, Finset.mem_insert] at hs
  obtain rfl | hs := hs
  · obtain rfl | he := e.eq_empty_or_nonempty
    · simp
    · exact ⟨e.max' he, fun _ ↦ le_max' _ _⟩
  · exact nonempty_of_mem_endpointPartitionIio hs

/-- If `e₁ ⊆ e₂`, then `endpointPartitionRight e₂` is a refinement of
`endpointPartitionLeft e₁`. -/
@[to_dual exists_subset_endpointPartitionLeft_of_subset
/-- If `e₁ ⊆ e₂`, then `endpointPartitionLeft e₂` is a refinement of
`endpointPartitionLeft e₁`. -/]
theorem exists_subset_endpointPartitionRight_of_subset {e₁ e₂ : Finset α} (h : e₁ ⊆ e₂) {s : Set α}
    (hs : s ∈ endpointPartitionRight e₂) : ∃ t ∈ endpointPartitionRight e₁, s ⊆ t := by
  simp_rw [mem_endpointPartitionRight_iff] at hs ⊢
  obtain rfl | ⟨x, hx₂, rfl⟩ := hs
  · refine ⟨_, .inl rfl, ?_⟩
    grind
  · by_cases hx₁ : x ∈ e₁
    · refine ⟨_, .inr ⟨x, hx₁, rfl⟩, ?_⟩
      grind
    obtain ⟨t, ht, hx⟩ := exists_endpointPartitionRight_mem e₁ x
    rw [mem_endpointPartitionRight_iff] at ht
    refine ⟨t, ht, fun y hy ↦ ?_⟩
    obtain rfl | ⟨z, hz, rfl⟩ := ht
    · intro z hz
      rw [← hy z (h hz)]
      apply (hx z hz).lt_of_ne
      rintro rfl
      contradiction
    · grind

/-- A lemma characterizing refinements where points are added in each existing interval. -/
@[to_dual exists_endpointPartitionLeft_inter_of_mem_union_image
/-- A lemma characterizing refinements where points are added in each existing interval. -/]
theorem exists_endpointPartitionRight_inter_of_mem_union_image {e : Finset α}
    (f : endpointPartitionRight e → α) (hf : ∀ t, f t ∈ t.1) {s : Set α}
    (hs : s ∈ endpointPartitionRight (e ∪ (endpointPartitionRight e).attach.image f)) :
    ∃ t : endpointPartitionRight e, s = t.1 ∩ Iio (f t) ∨ s = t.1 ∩ Ici (f t) := by
  rw [mem_endpointPartitionRight_iff] at hs
  obtain rfl | ⟨x, hx, rfl⟩ := hs
  · refine ⟨⟨_, Finset.mem_insert_self ..⟩, .inr ?_⟩
    ext x
    constructor
    · grind
    · dsimp
      grind
  · by_cases Hx : x ∈ e
    · let s : endpointPartitionRight e := ⟨_, mem_endpointPartitionRight_iff.2 (.inr ⟨x, Hx, rfl⟩)⟩
      refine ⟨s, ?_⟩
      obtain hx | hx := lt_or_ge x (f s)
      · left; grind
      right
      ext y
      refine ⟨?_, fun ⟨hy, hys⟩ z hz ↦ ?_⟩
      · grind
      · simp only [Finset.mem_union, Finset.mem_image, mem_attach, true_and, Subtype.exists] at hz
        obtain hz | ⟨t, ht, rfl⟩ := hz
        · exact hy z hz
        · refine ⟨fun htx ↦ hys.trans' ?_, fun hty ↦ hty.trans_lt ?_⟩
          · rw [mem_endpointPartitionRight_iff] at ht
            obtain rfl | ⟨t, ht, rfl⟩ := ht <;> grind
          · simpa using hy x Hx
    · simp only [Finset.mem_union, Finset.mem_image, mem_attach, true_and, Subtype.exists] at hx
      obtain hxe | ⟨s, hs, rfl⟩ := hx
      · contradiction
      refine ⟨⟨s, hs⟩, .inl ?_⟩
      ext x
      refine ⟨fun hx ↦ ⟨?_, ?_⟩, fun ⟨hx, hxf⟩ y hy ↦ ?_⟩
      · rw [mem_endpointPartitionRight_iff] at hs
        obtain rfl | ⟨y, hy, rfl⟩ := hs <;> grind
      · simpa using hx (f ⟨s, hs⟩)
      · simp only [Finset.mem_union, Finset.mem_image, mem_attach, true_and, Subtype.exists] at hy
        obtain hy | ⟨y, hy, rfl⟩ := hy
        · grind
        · refine ⟨fun hf' ↦ le_of_lt ?_, hxf.trans_le'⟩
          apply lt_of_mem_endpointPartitionRight hy hs _ (hf ⟨y, hy⟩) (hf ⟨s, hs⟩) hf'
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

@[simp] protected theorem empty : IsLinearOn f ∅ := by simp [IsLinearOn]

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

variable [LinearOrder K] [IsOrderedRing K]

theorem ordConnected_image (hf : IsLinearOn f s) (hs : s.OrdConnected) : (f '' s).OrdConnected where
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

private theorem max_inter_Iio (hf : IsLinearOn f s) {x : K} (hx : x ∈ s) (hfx : f x = 0) :
    IsLinearOn (max f 0) (s ∩ Iio x) := by
  obtain ⟨a, b, hf'⟩ := id hf
  obtain ha | ha := lt_or_ge a 0
  · refine ⟨a, b, fun y ⟨hy, hyx⟩ ↦ ?_⟩
    rw [Pi.sup_apply, Pi.zero_apply, hf' y hy, sup_eq_left, ← hfx, hf' x hx]
    simpa using mul_le_mul_of_nonpos_left hyx.le ha.le
  · refine ⟨0, 0, fun y ⟨hy, hyx⟩ ↦ ?_⟩
    rw [Pi.sup_apply, Pi.zero_apply, zero_mul, add_zero, sup_eq_right, hf' y hy, ← hfx, hf' x hx]
    simpa using mul_le_mul_of_nonneg_left hyx.le ha

@[to_dual existing]
private theorem min_inter_Ioi (hf : IsLinearOn f s) {x : K} (hx : x ∈ s) (hfx : f x = 0) :
    IsLinearOn (min f 0) (s ∩ Ioi x) := by
  obtain ⟨a, b, hf'⟩ := id hf
  obtain ha | ha := lt_or_ge a 0
  · refine ⟨a, b, fun y ⟨hy, hyx⟩ ↦ ?_⟩
    rw [Pi.inf_apply, Pi.zero_apply, hf' y hy, inf_eq_left, ← hfx, hf' x hx]
    simpa using mul_le_mul_of_nonpos_left hyx.le ha.le
  · refine ⟨0, 0, fun y ⟨hy, hyx⟩ ↦ ?_⟩
    rw [Pi.inf_apply, Pi.zero_apply, zero_mul, add_zero, inf_eq_right, hf' y hy, ← hfx, hf' x hx]
    simpa using mul_le_mul_of_nonneg_left hyx.le ha

private theorem max_inter_Ici (hf : IsLinearOn f s) {x : K} (hx : x ∈ s) (hfx : f x = 0) :
    IsLinearOn (max f 0) (s ∩ Ici x) := by
  obtain ⟨a, b, hf'⟩ := id hf
  obtain ha | ha := lt_or_ge a 0
  · refine ⟨0, 0, fun y ⟨hy, hyx⟩ ↦ ?_⟩
    rw [Pi.sup_apply, Pi.zero_apply, zero_mul, add_zero, sup_eq_right, hf' y hy, ← hfx, hf' x hx]
    simpa using mul_le_mul_of_nonpos_left hyx ha.le
  · refine ⟨a, b, fun y ⟨hy, hyx⟩ ↦ ?_⟩
    rw [Pi.sup_apply, Pi.zero_apply, hf' y hy, sup_eq_left, ← hfx, hf' x hx]
    simpa using mul_le_mul_of_nonneg_left hyx ha

@[to_dual existing]
private theorem min_inter_Iic (hf : IsLinearOn f s) {x : K} (hx : x ∈ s) (hfx : f x = 0) :
    IsLinearOn (min f 0) (s ∩ Iic x) := by
  obtain ⟨a, b, hf'⟩ := id hf
  obtain ha | ha := lt_or_ge a 0
  · refine ⟨0, 0, fun y ⟨hy, hyx⟩ ↦ ?_⟩
    rw [Pi.inf_apply, Pi.zero_apply, zero_mul, add_zero, inf_eq_right, hf' y hy, ← hfx, hf' x hx]
    simpa using mul_le_mul_of_nonpos_left hyx ha.le
  · refine ⟨a, b, fun y ⟨hy, hyx⟩ ↦ ?_⟩
    rw [Pi.inf_apply, Pi.zero_apply, hf' y hy, inf_eq_left, ← hfx, hf' x hx]
    simpa using mul_le_mul_of_nonneg_left hyx ha

end IsLinearOn

variable [LinearOrder K]

/-- A right-continuous piecewise linear function is one where there exists a finite set of
endpoints, such that the function is linear on each of the intervals they define. -/
@[to_dual IsPiecewiseLeftLinear
/-- A left-continuous piecewise linear function is one where there exists a finite set of
endpoints, such that the function is linear on each of the intervals they define. -/]
def IsPiecewiseRightLinear (f : K → K) : Prop :=
  ∃ e : Finset K, ∀ s ∈ LinearOrder.endpointPartitionRight e, IsLinearOn f s

namespace IsPiecewiseRightLinear
variable {f g : K → K}

open LinearOrder

@[to_dual]
protected theorem const (c : K) : IsPiecewiseRightLinear (const K c) :=
  ⟨∅, by simp⟩

@[to_dual]
protected theorem smul (x : K) (hf : IsPiecewiseRightLinear f) :
    IsPiecewiseRightLinear (x • f) := by
  obtain ⟨e, he⟩ := hf
  exact ⟨e, fun p hp ↦ (he p hp).smul x⟩

@[to_dual]
protected theorem qsmul (q : ℚ) (hf : IsPiecewiseRightLinear f) :
    IsPiecewiseRightLinear (q • f) := by
  obtain ⟨e, he⟩ := hf
  exact ⟨e, fun p hp ↦ (he p hp).qsmul q⟩

@[to_dual]
protected theorem zsmul (n : ℤ) (hf : IsPiecewiseRightLinear f) :
    IsPiecewiseRightLinear (n • f) := by
  obtain ⟨e, he⟩ := hf
  exact ⟨e, fun p hp ↦ (he p hp).zsmul n⟩

@[to_dual]
protected theorem nsmul (n : ℕ) (hf : IsPiecewiseRightLinear f) :
    IsPiecewiseRightLinear (n • f) := by
  obtain ⟨e, he⟩ := hf
  exact ⟨e, fun p hp ↦ (he p hp).nsmul n⟩

@[to_dual]
protected theorem neg (hf : IsPiecewiseRightLinear f) : IsPiecewiseRightLinear (-f) := by
  obtain ⟨e, he⟩ := hf
  use e
  simpa

@[to_dual (attr := simp)]
theorem neg_iff : IsPiecewiseRightLinear (-f) ↔ IsPiecewiseRightLinear f :=
  ⟨by simpa using IsPiecewiseRightLinear.neg (f := -f), IsPiecewiseRightLinear.neg⟩

protected theorem neg' (hf : IsPiecewiseRightLinear f) :
    IsPiecewiseLeftLinear (fun x ↦ f (-x)) := by
  sorry

@[to_dual]
protected theorem add (hf : IsPiecewiseRightLinear f) (hg : IsPiecewiseRightLinear g) :
    IsPiecewiseRightLinear (f + g) := by
  obtain ⟨e₁, he₁⟩ := hf
  obtain ⟨e₂, he₂⟩ := hg
  refine ⟨e₁ ∪ e₂, fun p hp ↦ ?_⟩
  obtain ⟨q, hq, hpq⟩ :=
    exists_subset_endpointPartitionRight_of_subset subset_union_left hp
  obtain ⟨r, hr, hpr⟩ :=
    exists_subset_endpointPartitionRight_of_subset subset_union_right hp
  exact ((he₁ q hq).anti hpq).add ((he₂ r hr).anti hpr)

@[to_dual]
protected theorem sub (hf : IsPiecewiseRightLinear f) (hg : IsPiecewiseRightLinear g) :
    IsPiecewiseRightLinear (f - g) := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

variable [IsOrderedRing K]

@[to_dual]
private theorem max_zero (hf : IsPiecewiseRightLinear f) : IsPiecewiseRightLinear (max f 0) := by
  classical
  obtain ⟨e, he⟩ := hf
  have H' (t : endpointPartitionRight e) (h0 : 0 ∉ f '' t.1) : IsLinearOn (max f 0) t.1 := by
    obtain ⟨a, b, hf⟩ := he _ t.2
    obtain ht | ⟨y, hy⟩ := t.1.eq_empty_or_nonempty
    · simp [ht]
    · have H := (he _ t.2).ordConnected_image (ordConnected_of_mem_endpointPartitionRight t.2)
      obtain hfy | hfy := lt_or_ge (f y) 0
      · refine ⟨0, 0, fun x hx ↦ ?_⟩
        rw [Pi.sup_apply, Pi.zero_apply, zero_mul, add_zero, sup_eq_right]
        contrapose! h0
        exact H.out (mem_image_of_mem _ hy) (mem_image_of_mem _ hx) ⟨hfy.le, h0.le⟩
      · refine ⟨a, b, fun x hx ↦ ?_⟩
        rw [Pi.sup_apply, Pi.zero_apply, ← hf x hx, sup_eq_left]
        contrapose! h0
        exact H.out (mem_image_of_mem _ hx) (mem_image_of_mem _ hy) ⟨h0.le, hfy⟩
  let g (t : endpointPartitionRight e) : K :=
    if hf : 0 ∈ f '' t.1 then hf.choose else (nonempty_of_mem_endpointPartitionRight t.2).choose
  use e ∪ (endpointPartitionRight e).attach.image g
  intro s hs
  obtain ⟨t, rfl | rfl⟩ := exists_endpointPartitionRight_inter_of_mem_union_image g (by grind) hs
  · dsimp [g]
    split_ifs with h0
    · obtain ⟨ht₁, ht₂⟩ := Exists.choose_spec h0
      exact (he _ t.2).max_inter_Iio ht₁ ht₂
    · exact IsLinearOn.anti inter_subset_left (H' t h0)
  · dsimp [g]
    split_ifs with h0
    · obtain ⟨ht₁, ht₂⟩ := Exists.choose_spec h0
      exact (he _ t.2).max_inter_Ici ht₁ ht₂
    · exact IsLinearOn.anti inter_subset_left (H' t h0)

protected theorem max (hf : IsPiecewiseRightLinear f) (hg : IsPiecewiseRightLinear g) :
    IsPiecewiseRightLinear (max f g) := by
  rw [← add_zero g, ← add_sub_cancel g f, ← add_sup]
  exact hg.add (hf.sub hg).max_zero

protected theorem min (hf : IsPiecewiseRightLinear f) (hg : IsPiecewiseRightLinear g) :
    IsPiecewiseRightLinear (min f g) := by
  simpa [← neg_inf] using hf.neg.max hg.neg

end IsPiecewiseRightLinear

namespace IsPiecewiseLeftLinear
variable {f g : K → K} [IsOrderedRing K]

@[to_dual existing]
protected theorem min (hf : IsPiecewiseLeftLinear f) (hg : IsPiecewiseLeftLinear g) :
    IsPiecewiseLeftLinear (min f g) := by
  rw [← add_zero g, ← add_sub_cancel g f, ← add_inf]
  exact hg.add (hf.sub hg).min_zero

@[to_dual existing]
protected theorem max (hf : IsPiecewiseLeftLinear f) (hg : IsPiecewiseLeftLinear g) :
    IsPiecewiseLeftLinear (max f g) := by
  simpa [← neg_sup] using hf.neg.min hg.neg

end IsPiecewiseLeftLinear

variable (K) in
/-- The subtype of left-continuous piecewise linear functions. -/
@[to_dual PiecewiseLeftLinear
/-- The subtype of right-continuous piecewise linear functions. -/]
abbrev PiecewiseRightLinear : Type _ := Subtype (IsPiecewiseRightLinear (K := K))

namespace PiecewiseRightLinear

@[to_dual]
instance : CoeFun (PiecewiseRightLinear K) (fun _ ↦ K → K) where
  coe := Subtype.val

@[to_dual]
theorem isPiecewiseLinear (f : PiecewiseRightLinear K) : IsPiecewiseRightLinear f :=
  f.2

@[to_dual (attr := ext)]
theorem ext {f g : PiecewiseRightLinear K} (H : ∀ x, f x = g x) : f = g :=
  Subtype.ext (funext H)

/-- The constant function as a piecewise linear function. -/
@[expose, to_dual]
protected def const (c : K) : PiecewiseRightLinear K :=
  ⟨_, .const c⟩

@[to_dual] instance : Zero (PiecewiseRightLinear K) := ⟨.const 0⟩
@[to_dual] instance : One (PiecewiseRightLinear K) := ⟨.const 1⟩

@[to_dual (attr := simp)] theorem coe_zero : (0 : PiecewiseRightLinear K) = (0 : K → K) := rfl
@[to_dual (attr := simp)] theorem coe_one : (1 : PiecewiseRightLinear K) = (1 : K → K) := rfl

@[to_dual]
instance : SMul K (PiecewiseRightLinear K) where
  smul x f := ⟨_, f.2.smul x⟩

@[to_dual]
instance : ZSMul (PiecewiseRightLinear K) where
  zsmul n f := ⟨_, f.2.zsmul n⟩

@[to_dual]
instance : NSMul (PiecewiseRightLinear K) where
  nsmul n f := ⟨_, f.2.nsmul n⟩

@[to_dual (attr := simp)]
theorem coe_smul (x : K) (f : PiecewiseRightLinear K) :
    (x • f : PiecewiseRightLinear K) = (x • f : K → K) :=
  rfl

@[to_dual (attr := simp)]
theorem coe_zsmul (n : ℤ) (f : PiecewiseRightLinear K) :
    (n • f : PiecewiseRightLinear K) = (n • f : K → K) :=
  rfl

@[to_dual (attr := simp)]
theorem coe_nsmul (n : ℕ) (f : PiecewiseRightLinear K) :
    (n • f : PiecewiseRightLinear K) = (n • f : K → K) :=
  rfl

@[to_dual]
instance : Add (PiecewiseRightLinear K) where
  add f g := ⟨_, f.2.add g.2⟩

@[to_dual (attr := simp)]
theorem coe_add (f g : PiecewiseRightLinear K) : (f + g : PiecewiseRightLinear K) = (f + g : K → K) :=
  rfl

@[to_dual]
instance : AddCommMonoidWithOne (PiecewiseRightLinear K) where
  zero_add f := by ext; exact zero_add ..
  add_zero f := by ext; exact add_zero ..
  add_comm f g := by ext; exact add_comm ..
  add_assoc f g h := by ext; exact add_assoc ..
  nsmul_zero f := by ext; simp
  nsmul_succ f n := by ext; simp [add_one_mul]

variable [IsOrderedRing K]

@[to_dual]
instance : Max (PiecewiseRightLinear K) where
  max f g := ⟨_, f.2.max g.2⟩

@[to_dual (attr := simp)]
theorem coe_sup (f g : PiecewiseRightLinear K) : (f ⊔ g : PiecewiseRightLinear K) = (f ⊔ g : K → K) :=
  rfl

@[to_dual]
instance : Min (PiecewiseRightLinear K) where
  min f g := ⟨_, f.2.min g.2⟩

@[to_dual (attr := simp)]
theorem coe_inf (f g : PiecewiseRightLinear K) : (f ⊓ g : PiecewiseRightLinear K) = (f ⊓ g : K → K) :=
  rfl

@[to_dual]
instance : Lattice (PiecewiseRightLinear K) where
  sup f g := f ⊔ g
  le_sup_left _ _ _  := le_sup_left
  le_sup_right _ _ _  := le_sup_right
  sup_le _f _g _h hfg hgh x := sup_le (hfg x) (hgh x)
  inf f g := f ⊓ g
  inf_le_left _ _ _  := inf_le_left
  inf_le_right _ _ _  := inf_le_right
  le_inf _f _g _h hfg hgh x := le_inf (hfg x) (hgh x)

/-! ### Continuity -/

/-- The slope and intercept of the line immediately to the right of `x`. -/
@[to_dual leftLine
/-- The slope and intercept of the line immediately to the left of `x`. -/]
def rightLine (f : PiecewiseRightLinear K) (x : K) : K × K :=
  have hs := LinearOrder.exists_endpointPartitionRight_mem f.2.choose x
  have he := f.2.choose_spec hs.choose hs.choose_spec.1
  ((Prod.exists (p := fun x ↦ ∀ y ∈ _, f y = x.1 * y + x.2)).2 he).choose

/-- The slope and intercept of the line immediately to the left of `x`. -/
def leftLine (f : PiecewiseRightLinear K) (x : K) : K × K :=
  rightLine f (Finset.exists_between' (f.2.choose.filter (· < x)) {x} (by simp)).choose

theorem rightLine_spec (f : PiecewiseRightLinear K) (x : K) :
    ∃ y, ∀ z ∈ Icc x y, f z = (rightLine f x).1 * z + (rightLine f x).2 := by
  sorry

theorem leftLine_spec (f : PiecewiseRightLinear K) (x : K) :
    ∃ y, ∀ z ∈ Ico y x, f z = (leftLine f x).1 * z + (leftLine f x).2 := by
  sorry

end PiecewiseRightLinear
end Function
