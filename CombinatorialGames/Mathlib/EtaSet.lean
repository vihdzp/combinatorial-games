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

public section

namespace Order
open Cardinal

universe u v

/--
If `α` is a type with a `LinearOrder`, and `c` is some `Cardinal` in the same universe, then
`IsEta c α` states that for any two subsets `X Y : Set α` of cardinality less than `c`, if every
element of `X` is less than every element of `Y`, then there is some `(z : α)` greater than all
elements of `X` and less than all elements of `Y`.

In the literature, an η_o ordered set would be a `IsEta ℵ_o` order, but this definition is more
general.
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

section

open IsEta OrderType

variable {α β : Type u} (a : α) [LT α] {r : α → α → Prop} (g : ∀ y, r y a → β)

/-- The Set β corresponding to the image of g with `x < a` -/
@[reducible]
def lo : Set β := Set.range fun (x : {x : α // r x a ∧ x < a}) ↦ g x.1 x.2.1

/-- The Set β corresponding to the image of g with `a < x` -/
@[reducible]
def hi : Set β := Set.range fun (x : {x : α // r x a ∧ a < x}) ↦ g x.1 x.2.1

theorem card_subtype_le {α : Type*} {r : α → α → Prop} [IsWellOrder α r]
    {h : (#α).ord = Ordinal.type r} : ∀ a, #{ x : α // r x a } < #α :=
  fun a ↦ Cardinal.card_typein_lt a h

theorem hlo_card {r : α → α → Prop} [IsWellOrder α r] (h : (#α).ord = Ordinal.type r) :
    ∀ a (g: ∀ y, r y a → β), #(lo (β := β) a g) < #α :=
  fun a _ ↦ Cardinal.mk_range_le.trans_lt ((Cardinal.mk_subtype_le_of_subset
    (fun _ hx ↦ hx.1)).trans_lt ((card_subtype_le (h:=h)) a))

theorem hhi_card {r : α → α → Prop} [IsWellOrder α r] (h : (#α).ord = Ordinal.type r) :
   ∀ a (g: ∀ y, r y a → β), #(hi (β := β) a g) < #α :=
  fun a _ ↦ Cardinal.mk_range_le.trans_lt ((Cardinal.mk_subtype_le_of_subset
    (fun _ hx ↦ hx.1)).trans_lt (card_subtype_le (h:=h) a))

open Classical in
/-- The map which will be an order embedding between `α` and `β`. -/
@[reducible]
noncomputable def IsEta.f {r : α → α → Prop} [Nonempty α] [LinearOrder β] [hr : IsWellOrder α r]
    (h : IsEta (#α) β) (hord : (#α).ord = Ordinal.type r) : α → β :=
  hr.wf.fix fun a g ↦ if hsep : ∀ b ∈ lo a g, ∀ c ∈ hi a g, b < c then
    (h.exists_between (hlo_card (h := hord) a g) (hhi_card hord a g) hsep).choose
  else (h.nonempty <| mk_ne_zero α).some

open Classical in
theorem f_aux (r : α → α → Prop) [Nonempty α] [LinearOrder α] [LinearOrder β]
   [hr : IsWellOrder α r] {h : IsEta #α β} {hord : (#α).ord = Ordinal.type r} :
   let f := h.f hord
   ∀ (a : α), f a =
   if hsep : ∀ b ∈ lo a (fun y _ ↦ f y), ∀ c ∈ hi a (fun y _ ↦ f y), b < c
   then (h.exists_between (s := (lo a fun y _ ↦ f y)) (t := hi a fun y _ ↦ f y)
      (hlo_card hord a (fun y _ ↦ f y))
      (hhi_card hord a (fun y _ ↦ f y)) hsep).choose
    else (h.nonempty <| mk_ne_zero α).some :=
  fun a ↦ by
  change hr.wf.fix _ a = _
  conv_lhs => rw [WellFounded.fix_eq]

theorem le_lo (r : α → α → Prop) [Nonempty α] [LinearOrder α] [LinearOrder β]
    [hr : IsWellOrder α r] {h : IsEta #α β} {hord : (#α).ord = Ordinal.type r} :
    let f := h.f hord
    ∀ (a : α) (hsep : ∀ x ∈ lo a fun y _ ↦ f y, ∀ y ∈ hi a fun y _ ↦ f y, x < y),
    ∀ x ∈ lo (r := r) a fun y _ ↦ f y, x < (exists_between h (hlo_card hord a fun y _ ↦ f y)
    (hhi_card hord a fun y _ ↦ f y) hsep).choose :=
  let f := h.f hord
  fun a hsep ↦ (h.exists_between (hlo_card hord a (fun y _ ↦ f y))
  (hhi_card hord a (fun y _ ↦ f y)) hsep).choose_spec.1

theorem hi_le (r : α → α → Prop) [Nonempty α] [LinearOrder α] [LinearOrder β]
    [hr : IsWellOrder α r] {h : IsEta #α β} {hord : (#α).ord = Ordinal.type r} :
    let f := h.f hord
    ∀ (a : α) (hsep : ∀ x ∈ lo (r:=r) a fun y _ ↦ f y, ∀ y ∈ hi a fun y _ ↦ f y, x < y),
    ∀ y ∈ hi (r:= r) a fun y _ ↦ f y, (exists_between h (hlo_card hord a fun y _ ↦ f y)
    (hhi_card hord a fun y _ ↦ f y) hsep).choose < y  :=
  let f := h.f hord
  fun a hsep ↦ (h.exists_between (hlo_card hord a (fun y _ ↦ f y))
  (hhi_card hord a (fun y _ ↦ f y)) hsep).choose_spec.2

theorem f_aux₁ {α β : Type u} (r : α → α → Prop) [Nonempty α] [LinearOrder α]
    [LinearOrder β] [hr : IsWellOrder α r] {h : IsEta #α β}
    {hord : (#α).ord = Ordinal.type r} (a : α) : let f := h.f hord
    (∀ b ∈ lo a (fun y (_ : r y a) ↦ f y), ∀ c ∈ hi a (fun y (_: r y a) ↦ f y),
    b < c) ∧ ∀ x y, r x a → r y a → x < y → f  x < f  y := by
  set f := f h hord
  have hunfold := f_aux (β := β) (hord:= hord) (h := h) r
  refine (hr.wf.induction (C := fun a ↦ (∀ b ∈ lo a fun y x ↦ f y, ∀ c ∈ hi a fun y x ↦ f y,
    b < c) ∧ ∀ (x y : α), r x a → r y a → x < y → f x < f y) a) (fun a IH ↦ ?_)
  refine ⟨fun b ⟨⟨x, hrxa, hxa⟩, hxeq⟩ _ ⟨⟨y, hrya, hay⟩, hyeq⟩ ↦ ?_, fun x y hrxa hrya hxy ↦ ?_⟩
  · simp only [← hxeq, ← hyeq]
    refine (@trichotomous_of α r _ x y).elim (fun hrxy ↦ ?_)
      (fun hor ↦ hor.elim (fun hxye ↦ (ne_of_lt (hxa.trans hay) hxye).elim) (fun hrya ↦ ?_))
      <;> rw [(by rfl : f = h.f hord)]
    · have hunfold := f_aux (β := β) (hord:=hord) (h := h) r
      rw [hunfold y, dif_pos (IH y hrya).1]
      exact le_lo r y (IH y hrya).1 (f x) ⟨⟨x, hrxy, hxa.trans hay⟩, rfl⟩
    · rw [hunfold x, dif_pos (IH x hrxa).1]
      exact hi_le r x (IH x hrxa).1 (f y) ⟨⟨y, hrya, hxa.trans hay⟩, rfl⟩
  · refine (@trichotomous_of α r _ x y).elim (fun hrxy ↦ ?_)
      (fun hor ↦ hor.elim (fun hxye ↦ (ne_of_lt hxy hxye).elim) (fun hryx ↦ ?_))
    <;> rw [(by rfl : f = h.f hord)]
    · rw [hunfold y, dif_pos (IH y hrya).1]
      exact le_lo r y (IH y hrya).1 (f x) ⟨⟨x, hrxy, hxy⟩, rfl⟩
    · rw [hunfold x, dif_pos (IH x hrxa).1]
      exact hi_le r x (IH x hrxa).1 (f y) ⟨⟨y, hryx, hxy⟩, rfl⟩

theorem strictMono_f {α β : Type u} [Nonempty α] (r : α → α → Prop) [IsWellOrder α r]
[LinearOrder α] [LinearOrder β] {hord : (#α).ord = Ordinal.type r} {h : IsEta #α β} :
    StrictMono (@f _ β _ r _ _ _ h hord) := fun {x y} hxy ↦ by
  rcases @trichotomous_of α r _ x y with hrxy | rfl | hryx
  <;> have hunfold := f_aux (β := β) (hord:=hord) (h := h) r
  <;> set f := f h hord
  · have hsep_y := (f_aux₁ (β := β) (hord := hord) (h := h) r y).1
    rw [hunfold y, dif_pos hsep_y]
    exact le_lo r y hsep_y (f x) ⟨⟨x, hrxy, hxy⟩, rfl⟩
  · exact absurd rfl (ne_of_lt hxy)
  · have hsep_x := (f_aux₁ (β := β) (hord := hord) (h := h) r x).1
    rw [hunfold x, dif_pos hsep_x]
    exact hi_le r x hsep_x (f y) ⟨⟨y, hryx, hxy⟩, rfl⟩

end

open OrderType

public theorem OrderType.type_le_type_of_isEta {α β : Type u} [LinearOrder α] [LinearOrder β]
    (h : IsEta #α β) : type α ≤ type β := by
  rcases Cardinal.exists_ord_eq α with ⟨r, hr, hord⟩
  rw [type_le_type_iff]
  by_cases hα : Nonempty α
  · exact ⟨(OrderEmbedding.ofStrictMono (h.f hord)
      (strictMono_f (h:=h) r))⟩
  · push Not at hα
    use @OrderEmbedding.ofIsEmpty α β _ _ _ |>.toEmbedding
    simp

end Order
