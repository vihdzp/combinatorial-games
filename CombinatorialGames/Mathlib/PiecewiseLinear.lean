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
theorem exists_endpointPartitionLeft_mem {e : Finset α} (x : α) :
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

/-- If `e₁ ⊆ e₂`, then `endpointPartitionLeft e₂` is a refinement of
`endpointPartitioLeft e₁`. -/
@[to_dual exists_subset_endpointPartitionRight_of_subset
/-- If `e₁ ⊆ e₂`, then `endpointPartitionRight e₂` is a refinement of
`endpointPartitionRight e₁`. -/]
theorem exists_subset_endpointPartitionLeft_of_subset {e₁ e₂ : Finset α} (h : e₁ ⊆ e₂) {s : Set α}
    (hs : s ∈ endpointPartitionLeft e₂) : ∃ t ∈ endpointPartitionLeft e₁, s ⊆ t := by
  simp_rw [mem_endpointPartitionLeft_iff] at hs ⊢
  obtain rfl | ⟨y, hy₂, rfl⟩ := hs
  · refine ⟨_, .inl rfl, ?_⟩
    grind
  · by_cases hy₁ : y ∈ e₁
    · refine ⟨_, .inr ⟨y, hy₁, rfl⟩, ?_⟩
      grind
    obtain ⟨t, ht, hy⟩ := exists_endpointPartitionLeft_mem y
    rw [mem_endpointPartitionLeft_iff] at ht
    refine ⟨t, ht, fun x hx ↦ ?_⟩
    obtain rfl | ⟨z, hz, rfl⟩ := ht
    · intro z hz
      rw [← hx z (h hz)]
      apply (hy z hz).lt_of_ne
      rintro rfl
      contradiction
    · grind

end LinearOrder

namespace Finpartition

variable {α : Type*} [LinearOrder α]

private def ofEndpointsPartsAux : List α → Finset (Set α)
  | [] => {}
  | [a] => {Ioi a}
  | a :: b :: l => insert (Ioc a b) (ofEndpointsPartsAux (b :: l))

@[simp]
private theorem ofEndpointsPartsAux_nil : ofEndpointsPartsAux (α := α) [] = {} :=
  rfl

@[simp]
private theorem ofEndpointsPartsAux_singleton (a : α) : ofEndpointsPartsAux [a] = {Ioi a} :=
  rfl

private theorem Ioi_subset_sup_ofEndpointsPartsAux_cons (a : α) (l : List α) :
    Ioi a ⊆ (ofEndpointsPartsAux (a :: l)).sup id := by
  induction l generalizing a with
  | nil => simp
  | cons b l IH =>
    rw [ofEndpointsPartsAux, sup_insert, id]
    grw [← IH, Ioi_subset_Ioc_union_Ioi]

private theorem sup_ofEndpointsPartsAux_cons {a : α} {l : List α} (hl : (a :: l).SortedLE) :
    (ofEndpointsPartsAux (a :: l)).sup id = Ioi a := by
  induction l generalizing a with
  | nil => simp
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
  | nil => simp
  | cons a l =>
    induction l generalizing a with
    | nil => simp
    | cons b l IH =>
      rw [ofEndpointsPartsAux, coe_insert, pairwiseDisjoint_insert]
      rw [List.sortedLE_cons] at hl
      refine ⟨IH _ hl.2, fun s hs _ ↦ ?_⟩
      apply Set.disjoint_of_subset_right _ (Ioc_disjoint_Ioi le_rfl)
      rw [← sup_ofEndpointsPartsAux_cons hl.2]
      exact le_sup hs

private theorem empty_notMem_ofEndpointsPartsAux [NoMaxOrder α] :
    ∀ {l : List α} (_ : l.SortedLT), ∅ ∉ ofEndpointsPartsAux l
  | [] => by simp
  | [a] => by simp [← nonempty_iff_empty_ne]
  | a :: b :: l => by
    rw [List.sortedLT_cons]
    intro ⟨hl₁, hl₂⟩
    rw [ofEndpointsPartsAux, Finset.mem_insert, not_or]
    refine ⟨?_, empty_notMem_ofEndpointsPartsAux hl₂⟩
    rw [← ne_eq, ← nonempty_iff_empty_ne, nonempty_Ioc]
    exact hl₁ _ List.mem_cons_self

private theorem ordConnected_of_mem_ofEndpointsPartsAux {l : List α} {s : Set α}
    (hs : s ∈ ofEndpointsPartsAux l) : s.OrdConnected := by
  cases l with
  | nil => simp_all
  | cons a l =>
    induction l generalizing a with
    | nil => simp_all [ordConnected_Ioi]
    | cons b l IH =>
      rw [ofEndpointsPartsAux, Finset.mem_insert] at hs
      obtain rfl | hs := hs
      · exact ordConnected_Ioc
      · exact IH b hs

private theorem setOfPred_forall_cons_lt_iff_le {a y : α} {l : List α}
    (hy : y ∈ l) (hl : (a :: l).SortedLT) :
    {x | ∀ z ∈ a :: l, y < z ↔ x ≤ z} = {x | ∀ z ∈ l, y < z ↔ x ≤ z} := by
  ext x
  refine ⟨by simp, fun hx z hz ↦ ?_⟩
  rw [List.mem_cons] at hz
  obtain rfl | hz := hz
  · rw [List.sortedLT_cons] at hl
    have hz := hl.1 y hy
    apply iff_of_false hz.asymm (hz.trans _).not_ge
    rw [← not_le, ← hx y hy]
    exact lt_irrefl y
  · exact hx z hz

private theorem setOfPred_forall_cons_cons_lt_iff_le {a b : α} {l : List α}
    (hl : (a :: b :: l).SortedLT) :
    {x | ∀ z ∈ a :: b :: l, a < z ↔ x ≤ z} = Ioc a b := by
  rw [List.sortedLT_cons, List.sortedLT_cons] at hl
  ext x
  refine ⟨fun hx ↦ ⟨?_, ?_⟩, by grind⟩
  · rw [← not_le, ← hx] <;> simp
  · rw [← hx b (by simp)]
    exact hl.1 b List.mem_cons_self

private theorem mem_ofEndpointsPartsAux_iff {l : List α} (hl : l.SortedLT)
    {s : Set α} : s ∈ ofEndpointsPartsAux l ↔ ∃ y ∈ l, s = {x | ∀ z ∈ l, y < z ↔ x ≤ z} := by
  cases l with
  | nil => simp
  | cons a l =>
    induction l generalizing a with
    | nil => simp [Ioi_def]
    | cons b l IH =>
      rw [ofEndpointsPartsAux, Finset.mem_insert]
      constructor
      · rintro (rfl | hs)
        · exact ⟨a, List.mem_cons_self, (setOfPred_forall_cons_cons_lt_iff_le hl).symm⟩
        · rw [IH _ hl.of_cons] at hs
          obtain ⟨x, hx, rfl⟩ := hs
          exact ⟨x, List.mem_cons_of_mem _ hx, (setOfPred_forall_cons_lt_iff_le hx hl).symm⟩
      · rintro ⟨y, hy, rfl⟩
        rw [List.mem_cons] at hy
        obtain rfl | hy := hy
        · exact .inl <| setOfPred_forall_cons_cons_lt_iff_le hl
        · exact .inr <| (IH b hl.of_cons).2 ⟨y, hy, setOfPred_forall_cons_lt_iff_le hy hl⟩

-- TODO: come up with better name?
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

theorem ordConnected_of_mem_ofEndpointsParts {l : List α} {s : Set α}
    (hs : s ∈ ofEndpointsParts l) : s.OrdConnected := by
  cases l with
  | nil => simp_all [ordConnected_univ]
  | cons a l =>
    rw [ofEndpointsParts, Finset.mem_insert] at hs
    obtain rfl | hs := hs
    · exact ordConnected_Iic
    · exact ordConnected_of_mem_ofEndpointsPartsAux hs

theorem mem_ofEndpointsParts_iff {l : List α} (hl : l.SortedLT)
    {s : Set α} : s ∈ ofEndpointsParts l ↔
      s = {x | ∀ z ∈ l, x ≤ z} ∨ ∃ y ∈ l, s = {x | ∀ z ∈ l, y < z ↔ x ≤ z} := by
  cases l with
  | nil => simp
  | cons a l =>
    rw [ofEndpointsParts, Finset.mem_insert]
    apply or_congr _ (mem_ofEndpointsPartsAux_iff hl)
    congr! 1
    ext x
    refine ⟨fun hx y hy ↦ ?_, fun hx ↦ hx a List.mem_cons_self⟩
    rw [List.mem_cons] at hy
    obtain rfl | hy := hy
    · exact hx
    · rw [List.sortedLT_cons] at hl
      exact hx.trans (hl.1 y hy).le

/-- Partition a linear order into intervals `Iic`, `Ioc`, and `Ioi` using a finset of endpoints. -/
def ofEndpoints (e : Finset α) : Finpartition (.univ : Set α) where
  parts := (ofEndpointsParts (e.sort (· ≤ ·))).erase ∅
  supIndep :=
    (pairwiseDisjoint_ofEndpointsParts (sortedLT_sort _).sortedLE).supIndep.subset (erase_subset ..)
  sup_parts := by rw [← Set.bot_eq_empty, sup_erase_bot, sup_ofEndpointsParts]
  bot_notMem := notMem_erase _ _

private theorem parts_ofEndpoints' (e : Finset α) :
    (ofEndpoints e).parts = (ofEndpointsParts (e.sort (· ≤ ·))).erase ∅ :=
  (rfl)

private theorem parts_ofEndpoints [Nonempty α] [NoMaxOrder α] (e : Finset α) :
    (ofEndpoints e).parts = ofEndpointsParts (e.sort (· ≤ ·)) :=
  Finset.erase_eq_of_notMem <| empty_notMem_ofEndpointsParts (sortedLT_sort _)

@[simp]
theorem ofEndpoints_empty [Nonempty α] : ofEndpoints (α := α) ∅ = indiscrete (by simp) := by
  ext; simp +contextual [parts_ofEndpoints']

theorem ordConnected_of_mem_parts_ofEndpoints {e : Finset α} {s : Set α}
    (hx : s ∈ (ofEndpoints e).parts) : s.OrdConnected :=
  ordConnected_of_mem_ofEndpointsParts (mem_of_mem_erase hx)

theorem mem_parts_ofEndpoint_iff [Nonempty α] [NoMaxOrder α] {e : Finset α}
    {s : Set α} : s ∈ (ofEndpoints e).parts ↔
      s = {x | ∀ z ∈ e, x ≤ z} ∨ ∃ y ∈ e, s = {x | ∀ z ∈ e, y < z ↔ x ≤ z} := by
  rw [parts_ofEndpoints, mem_ofEndpointsParts_iff (sortedLT_sort _)]
  simp

/-- If `e₁ ⊆ e₂`, then `ofEndpoints e₂` is a refinement of `ofEndpoints e₁`. -/
theorem exists_subset_parts_ofEndpoints_of_subset [Nonempty α] [NoMaxOrder α]
    {e₁ e₂ : Finset α} (h : e₁ ⊆ e₂) {s : Set α} (hs : s ∈ (ofEndpoints e₂).parts) :
    ∃ t ∈ (ofEndpoints e₁).parts, s ⊆ t := by
  rw [mem_parts_ofEndpoint_iff] at hs
  obtain rfl | ⟨y, hy₂, rfl⟩ := hs
  · refine ⟨{x | ∀ z ∈ e₁, x ≤ z}, ?_, ?_⟩
    · rw [mem_parts_ofEndpoint_iff]
      exact .inl rfl
    · grind
  · by_cases hy₁ : y ∈ e₁
    · refine ⟨{x | ∀ z ∈ e₁, y < z ↔ x ≤ z}, ?_, ?_⟩
      · rw [mem_parts_ofEndpoint_iff]
        exact .inr ⟨y, hy₁, rfl⟩
      · grind
    obtain ⟨t, ht, hy⟩ : ∃ t ∈ (ofEndpoints e₁).parts, y ∈ t := by
      simpa using Set.ext_iff.1 (ofEndpoints e₁).sup_parts y
    refine ⟨t, ht, fun x hx ↦ ?_⟩
    rw [mem_parts_ofEndpoint_iff] at ht
    obtain rfl | ⟨z, hz, rfl⟩ := ht
    · intro z hz
      rw [← hx z (h hz)]
      apply (hy z hz).lt_of_ne
      rintro rfl
      contradiction
    · grind

end Finpartition

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
    IsPiecewiseLinear (f + g) := by
  obtain ⟨s, hs⟩ := hf
  obtain ⟨t, ht⟩ := hg
  refine ⟨s ∪ t, fun p hp ↦ ?_⟩
  obtain ⟨q, hq, hpq⟩ :=
    Finpartition.exists_subset_parts_ofEndpoints_of_subset subset_union_left hp
  obtain ⟨r, hr, hpr⟩ :=
    Finpartition.exists_subset_parts_ofEndpoints_of_subset subset_union_right hp
  exact ((hs q hq).anti hpq).add ((ht r hr).anti hpr)

protected theorem sub (hf : IsPiecewiseLinear f) (hg : IsPiecewiseLinear g) :
    IsPiecewiseLinear (f - g) := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

private theorem max_zero (hf : IsPiecewiseLinear f) : IsPiecewiseLinear (max f 0) := by
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
