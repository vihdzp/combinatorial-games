/-
Copyright (c) 2026 Yan Yablonovskiy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yan Yablonovskiy
-/
module

public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Data.Finset.DenselyOrdered
public import Mathlib.Order.CountableDenseLinearOrder
public import Mathlib.Order.Types.Defs
public import Mathlib.SetTheory.Ordinal.Basic

namespace Order
open Cardinal

universe u v

@[expose] public section

/--
If `α` is a type with a `LinearOrder` , and `c` is some `Cardinal` in the same universe, then
`IsEta c α` states that for any two subsets
`X Y : Set α` of cardinality less than `c`, if every element of
`X` is less than every element of `Y`, then there is some `(z : α)`
greater than all elements of `X` and less than all elements of
`Y`.

In the literature, an η_α ordered set would be a `IsEta ℵ_α` order,
but this definition is more general.
-/
def IsEta (c : Cardinal.{u}) (α : Type u) [LinearOrder α] : Prop :=
  ∀ ⦃s t : Set α⦄, #s < c → #t < c →
    (∀ x ∈ s, ∀ y ∈ t, x < y) → ∃ z, (∀ x ∈ s, x < z) ∧ (∀ y ∈ t, z < y)

namespace IsEta

open Order OrderType

variable {α β γ : Type u} [LinearOrder α] [LinearOrder β] [LinearOrder γ] {c c' : Cardinal.{u}}

/-- `IsEta` is unchanged under the order dual. -/
theorem isEta_dual (c : Cardinal.{u}) (α : Type u) [LinearOrder α] : IsEta c α ↔ IsEta c αᵒᵈ :=
  ⟨fun hη _ _ hs ht hst ↦
    let ⟨z, hz⟩ := hη ht hs (fun x hT y hS ↦ hst y hS x hT); ⟨z, hz.symm⟩,
  fun hη _ _ hs ht hst ↦
    let ⟨z, hz⟩ := hη ht hs (fun x hT y hS ↦ hst y hS x hT); ⟨z, hz.symm⟩⟩

protected alias ⟨_, dual⟩ := isEta_dual

to_dual_insert_cast IsEta := propext (isEta_dual c α)
  rfl

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

/-- If `α` is nonempty and `β` satisfies `IsEta #α β`, then `β` is nonempty. -/
protected theorem nonempty (hc : c ≠ 0) (h : IsEta c α) : Nonempty α := by
  simpa [hc.pos] using @h ∅ ∅

/-- The η property implies density when the cardinal is larger than 1. -/
protected theorem denselyOrdered (hc : 1 < c) (h : IsEta c α) : DenselyOrdered α where
  dense x y hxy := by simpa [hc, hxy] using @h {x} {y}

@[to_dual]
protected theorem noMinOrder (hc : 1 < c) (h : IsEta c α) : NoMinOrder α where
  exists_lt x := by simpa [hc, hc.pos] using @h ∅ {x}

open Classical in
/-- When `1 < c`, an `IsEta c` linear order is nontrivial. -/
protected theorem nontrivial (hc : 1 < c) (h : IsEta c α) [Nonempty α] : Nontrivial α := by
  obtain ⟨b⟩ := ‹Nonempty α›
  obtain ⟨z, hbz, _⟩ :=
    exists_between h (s := {b}) (t := ∅) (by simpa)
    (by rw [mk_eq_zero]; exact bot_lt_iff_ne_bot.2 (ne_of_gt (lt_trans zero_lt_one hc))) (by simp)
  exact nontrivial_of_lt b z (hbz b (Set.mem_singleton b))

private theorem of_isEta_iso (e : α ≃o β) : IsEta c α → IsEta c β := fun H s t hs ht hsep ↦ by
  obtain ⟨z, hz₁, hz₂⟩ := by
    refine @H (e.symm '' s) (e.symm '' t) ?_ ?_ (fun a ⟨x, hx, ((hex: e.symm x = a))⟩ b
      ⟨y, hy, (hey : e.symm y = b)⟩ ↦ by
        simpa [e.lt_iff_lt,←hex,←hey] using hsep x hx y hy) <;>
    simpa [mk_image_eq e.symm.injective]
  refine ⟨e z, fun x hx ↦ ?_, fun y hy ↦ ?_⟩
  · grind [e.apply_symm_apply,(e.lt_iff_lt).mpr,(e.lt_iff_lt).mpr (hz₁ (e.symm x) ⟨x, hx, rfl⟩)]
  · simpa [e.apply_symm_apply] using (e.lt_iff_lt).mpr (hz₂ (e.symm y) ⟨y, hy, rfl⟩)

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

end

end Order
