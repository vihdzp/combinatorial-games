/-
Copyright (c) 2026 Yan Yablonovskiy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yan Yablonovskiy
-/
module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Data.Finset.DenselyOrdered
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Order.Types.Defs
public import Mathlib.SetTheory.Ordinal.Basic

/-!
# Eta sets

If `α` is a type with a `LinearOrder`, and `c` is some `Cardinal` in the same universe, then
`IsEta c α` states that for any two subsets `X Y : Set α` of cardinality less than `c`, if every
element of `X` is less than every element of `Y`, then there is some `(z : α)` greater than all
elements of `X` and less than all elements of `Y`.

Every linear order is vacuously `IsEta 0`. For `1 ≤ c ≤ ℵ₀`, the predicate `IsEta c` is equivalent
to having a densely ordered linear order. Examples of `IsEta c` orders for uncountable `c` include
the surreals and the hyperreals.

In the literature, an η_o ordered set would be a `IsEta ℵ_o` order, but this definition is more
general.
-/

public section

namespace Order
open Cardinal

universe u v

/--
If `α` is a type with a `LinearOrder`, and `c` is some `Cardinal` in the same universe, then
`IsEta c α` states that for any two subsets `X Y : Set α` of cardinality less than `c`, if every
element of `X` is less than every element of `Y`, then there is some `(z : α)` greater than all
elements of `X` and less than all elements of `Y`.
-/
@[expose]
def IsEta (c : Cardinal.{u}) (α : Type u) [LinearOrder α] : Prop :=
  ∀ ⦃s t : Set α⦄, #s < c → #t < c →
    (∀ x ∈ s, ∀ y ∈ t, x < y) → ∃ z, (∀ x ∈ s, x < z) ∧ (∀ y ∈ t, z < y)

namespace IsEta

open Order OrderType

variable {α β γ : Type u} [LinearOrder α] [LinearOrder β] [LinearOrder γ] {c c' : Cardinal.{u}}

/-- `IsEta` is unchanged under the order dual. -/
theorem dual_iff : IsEta c α ↔ IsEta c αᵒᵈ := by
  refine ⟨?_, ?_⟩ <;>
  exact fun hη _ _ hs ht hst ↦
    let ⟨z, hz⟩ := hη ht hs (fun x hT y hS ↦ hst y hS x hT); ⟨z, hz.symm⟩

protected alias ⟨_, dual⟩ := dual_iff

to_dual_insert_cast IsEta := propext dual_iff

@[to_dual none]
theorem exists_between (h : IsEta c α) {s t : Set α} (hs : #s < c) (ht : #t < c)
    (hB : ∀ x ∈ s, ∀ y ∈ t, x < y) : ∃ z, (∀ x ∈ s, x < z) ∧ (∀ y ∈ t, z < y) :=
  h hs ht hB

protected theorem zero : IsEta 0 α :=
  fun _ _ hs ↦ (not_lt_bot hs).elim

protected theorem mono (h : IsEta c α) (hc : c' ≤ c) : IsEta c' α :=
  fun _ _ hs ht hB ↦ h (hs.trans_le hc) (ht.trans_le hc) hB

protected theorem one [Nonempty α] : IsEta 1 α :=
  fun s ↦ by simp +contextual [mk_eq_zero_iff]

protected theorem nonempty (hc : c ≠ 0) (h : IsEta c α) : Nonempty α := by
  simpa [hc.pos] using @h ∅ ∅

protected theorem denselyOrdered (hc : 1 < c) (h : IsEta c α) : DenselyOrdered α where
  dense x y hxy := by simpa [hc, hxy] using @h {x} {y}

@[to_dual]
protected theorem noMinOrder (hc : 1 < c) (h : IsEta c α) : NoMinOrder α where
  exists_lt x := by simpa [hc, hc.pos] using @h ∅ {x}

protected theorem infinite (hc : 1 < c) (h : IsEta c α) [Nonempty α] : Infinite α :=
  h.noMinOrder hc |>.infinite

private theorem of_isEta_iso (e : α ≃o β) : IsEta c α → IsEta c β := fun H s t hs ht hsep ↦ by
  rw [← e.exists_congr_right]
  simpa +contextual [mk_image_eq e.symm.injective, e.symm_apply_lt, e.lt_symm_apply, *] using
    @H (e.symm '' s) (e.symm '' t)

/-- Order-isomorphic linear orders satisfy `IsEta` for the same cardinal. -/
protected theorem congr (e : α ≃o β) : IsEta c α ↔ IsEta c β :=
  ⟨of_isEta_iso e, of_isEta_iso e.symm⟩

theorem orderType_eq (h : type α = type β) : IsEta c α = IsEta c β :=
  propext <| IsEta.congr (type_eq_type.mp h).some

protected theorem aleph0 [Nonempty α] [DenselyOrdered α] [NoMaxOrder α] [NoMinOrder α] :
    IsEta aleph0 α := fun s t hs ht hB ↦ by
  rw [Cardinal.lt_aleph0_iff_finite] at *
  exact Set.Finite.exists_between' hs ht hB

theorem Rat.isEta_aleph0 : IsEta aleph0 ℚ := .aleph0

end IsEta

end Order
