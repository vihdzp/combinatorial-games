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

Every linear order is vacuously `IsEta 0`, and the `IsEta 1` predicate is equivalent to `Nonempty`.
For `1 < c ≤ ℵ₀`, the predicate `IsEta c` is equivalent to `DenselyOrdered`. Examples of `IsEta c`
orders for uncountable `c` include the surreals and the hyperreals.

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

section BackAndForth

variable {r : α → α → Prop}

/-- The image under `g` of the `r`-predecessors of `a` lying below `a`. -/
private def lo (a : α) (g : ∀ y, r y a → β) : Set β :=
  Set.range fun x : {x : α // r x a ∧ x < a} ↦ g x.1 x.2.1

/-- The image under `g` of the `r`-predecessors of `a` lying above `a`. -/
private def hi (a : α) (g : ∀ y, r y a → β) : Set β :=
  Set.range fun x : {x : α // r x a ∧ a < x} ↦ g x.1 x.2.1

private theorem card_subtype_lt {δ : Type v} {t : δ → δ → Prop} [IsWellOrder δ t]
    (h : (#δ).ord = Ordinal.type t) (x : δ) : #{y : δ // t y x} < #δ :=
  Cardinal.card_typein_lt x h

variable [hr : IsWellOrder α r]

omit [LinearOrder β] in
private theorem mk_lo_lt (hord : (#α).ord = Ordinal.type r) (a : α) (g : ∀ y, r y a → β) :
    #(lo a g) < #α :=
  mk_range_le.trans_lt <| (mk_subtype_le_of_subset fun _ hx ↦ hx.1).trans_lt <|
    card_subtype_lt hord a

omit [LinearOrder β] in
private theorem mk_hi_lt (hord : (#α).ord = Ordinal.type r) (a : α) (g : ∀ y, r y a → β) :
    #(hi a g) < #α :=
  mk_range_le.trans_lt <| (mk_subtype_le_of_subset fun _ hx ↦ hx.1).trans_lt <|
    card_subtype_lt hord a

open Classical in
/-- The function which will be shown to be either just an order embedding,
or potentially an order isomorphism if the cardinalities of β and α are equal. -/
@[reducible]
private noncomputable def f [Nonempty α] (h : IsEta #α β) (hord : (#α).ord = Ordinal.type r)
    (s : β → β → Prop) [hs : IsWellOrder β s] : α → β :=
  hr.wf.fix fun a g ↦
    if hsep : ∀ x ∈ lo a g, ∀ y ∈ hi a g, x < y then
      hs.wf.min {z | (∀ x ∈ lo a g, x < z) ∧ ∀ y ∈ hi a g, z < y}
        (h.exists_between (mk_lo_lt hord a g) (mk_hi_lt hord a g) hsep)
    else (h.nonempty <| have : Nonempty α := ⟨a⟩; mk_ne_zero α).some

variable [Nonempty α] {s : β → β → Prop} [hs : IsWellOrder β s] {h : IsEta #α β}
  {hord : (#α).ord = Ordinal.type r}

open Classical in
private theorem f_def (a : α) :
    h.f hord s a =
      if hsep : ∀ x ∈ lo a fun y (_ : r y a) ↦ h.f hord s y,
          ∀ y ∈ hi a fun y (_ : r y a) ↦ h.f hord s y, x < y then
        hs.wf.min
          {z | (∀ x ∈ lo a fun y (_ : r y a) ↦ h.f hord s y, x < z) ∧
            ∀ y ∈ hi a fun y (_ : r y a) ↦ h.f hord s y, z < y}
          (h.exists_between (mk_lo_lt hord a _) (mk_hi_lt hord a _) hsep)
      else (h.nonempty <| mk_ne_zero α).some :=
  hr.wf.fix_eq _ a

private theorem f_mem (a : α)
    (hsep : ∀ x ∈ lo a fun y (_ : r y a) ↦ h.f hord s y,
      ∀ y ∈ hi a fun y (_ : r y a) ↦ h.f hord s y, x < y) :
    (∀ x ∈ lo a fun y (_ : r y a) ↦ h.f hord s y, x < h.f hord s a) ∧
      ∀ y ∈ hi a fun y (_ : r y a) ↦ h.f hord s y, h.f hord s a < y := by
  rw [f_def a, dif_pos hsep]
  exact hs.wf.min_mem
    {z | (∀ x ∈ lo a fun y (_ : r y a) ↦ h.f hord s y, x < z) ∧
      ∀ y ∈ hi a fun y (_ : r y a) ↦ h.f hord s y, z < y} _

private theorem f_sep (a : α) :
    ∀ x ∈ lo a fun y (_ : r y a) ↦ h.f hord s y,
      ∀ y ∈ hi a fun y (_ : r y a) ↦ h.f hord s y, x < y := by
  induction a using hr.wf.induction with
  | h a IH =>
    rintro _ ⟨⟨x, hrx, hxa⟩, rfl⟩ _ ⟨⟨y, hry, hay⟩, rfl⟩
    dsimp
    have hxy := hxa.trans hay
    rcases trichotomous_of r x y with hrxy | rfl | hryx
    --repetitive, single grind almost works except the .1 amd .2 and providing the arguments somehow
    · exact (f_mem y (IH y hry)).1 _ ⟨⟨x, hrxy, hxy⟩, rfl⟩
    · cases hxy.false
    · exact (f_mem x (IH x hrx)).2 _ ⟨⟨y, hryx, hxy⟩, rfl⟩

private theorem strictMono_f : StrictMono (h.f hord s) := fun x y hxy ↦ by
  rcases trichotomous_of r x y with hrxy | rfl | hryx
  · exact (f_mem y (f_sep y)).1 _ ⟨⟨x, hrxy, hxy⟩, rfl⟩
  · cases hxy.false
  · exact (f_mem x (f_sep x)).2 _ ⟨⟨y, hryx, hxy⟩, rfl⟩

private theorem not_lt_f {z : β} (a : α)
    (hz : (∀ x ∈ lo a fun y (_ : r y a) ↦ h.f hord s y, x < z) ∧
      ∀ y ∈ hi a fun y (_ : r y a) ↦ h.f hord s y, z < y) :
    ¬s z (h.f hord s a) := by
  rw [f_def a, dif_pos (f_sep a)]
  exact hs.wf.not_lt_min _ hz

private theorem surjective_f (hα : IsEta #α α) (hords : (#β).ord = Ordinal.type s)
    (heq : #α = #β) :
    Function.Surjective (h.f hord s) := by
  intro b
  by_contra hb
  push Not at hb
  have hmono : StrictMono (h.f hord s) := strictMono_f
  set A : Set α := {a | s (h.f hord s a) b}
  set Alo : Set α := {a ∈ A | h.f hord s a < b}
  set Ahi : Set α := {a ∈ A | b < h.f hord s a}
  have hA : #A < #α :=
    ((mk_le_of_injective (f := fun a : A ↦ (⟨h.f hord s a.1, a.2⟩ : {c : β // s c b}))
      fun a₁ a₂ he ↦ Subtype.ext (hmono.injective (congrArg Subtype.val he))).trans_lt
      (card_subtype_lt hords b)).trans_eq heq.symm
  have hS : {z | (∀ x ∈ Alo, x < z) ∧ ∀ y ∈ Ahi, z < y}.Nonempty :=
    hα ((mk_le_mk_of_subset fun _ hx ↦ hx.1).trans_lt hA)
      ((mk_le_mk_of_subset fun _ hx ↦ hx.1).trans_lt hA)
      fun x hx y hy ↦ hmono.lt_iff_lt.1 (hx.2.trans hy.2)
  obtain ⟨a₀, ⟨hlo₀, hhi₀⟩, hmin⟩ := hr.wf.has_min _ hS
  have hcand₁ : ∀ x ∈ lo a₀ fun y (_ : r y a₀) ↦ h.f hord s y, x < b := by
    rintro _ ⟨⟨x, hrx, hxa⟩, rfl⟩
    change h.f hord s x < b
    have hxS : ¬((∀ w ∈ Alo, w < x) ∧ ∀ w ∈ Ahi, x < w) := fun hxS ↦ hmin x hxS hrx
    rcases not_and_or.mp hxS with hno | hno <;> push Not at hno <;> obtain ⟨w, hw, hwx⟩ := hno
    · exact (hmono.monotone hwx).trans_lt hw.2
    · exact absurd ((hhi₀ w hw).trans_le hwx) hxa.asymm
  have hcand₂ : ∀ y ∈ hi a₀ fun y (_ : r y a₀) ↦ h.f hord s y, b < y := by
    rintro _ ⟨⟨y, hry, hay⟩, rfl⟩
    change b < h.f hord s y
    have hyS : ¬((∀ w ∈ Alo, w < y) ∧ ∀ w ∈ Ahi, y < w) := fun hyS ↦ hmin y hyS hry
    rcases not_and_or.mp hyS with hno | hno <;> push Not at hno <;> obtain ⟨w, hw, hwy⟩ := hno
    · exact absurd (hwy.trans_lt (hlo₀ w hw)) hay.asymm
    · exact hw.2.trans_le (hmono.monotone hwy)
  have hfa₀ : s (h.f hord s a₀) b := (trichotomous_of s _ b).resolve_right <|
    not_or.2 ⟨hb a₀, not_lt_f a₀ ⟨hcand₁, hcand₂⟩⟩
  rcases lt_or_gt_of_ne (hb a₀) with h' | h'
  --couldnt get grind to play nice here either, even though its so repetitive
  · exact (hlo₀ a₀ ⟨hfa₀, h'⟩).false
  · exact (hhi₀ a₀ ⟨hfa₀, h'⟩).false

end BackAndForth

end IsEta

open IsEta OrderType
/-- If `β` is an `η_c` set, any linear order of cardinal `c` embeds into it.  -/
public theorem OrderType.type_le_type_of_isEta {α β : Type u} [LinearOrder α] [LinearOrder β]
    (h : IsEta #α β) : type α ≤ type β := by
  cases isEmpty_or_nonempty α with
  | inl _ => exact type_le_type_iff.2 ⟨.ofIsEmpty⟩
  | inr _ =>
    obtain ⟨r, hr, hord⟩ := Cardinal.exists_ord_eq α
    obtain ⟨s, hs, -⟩ := Cardinal.exists_ord_eq β
    exact type_le_type_iff.2 ⟨.ofStrictMono _ (strictMono_f (h := h) (hord := hord) (s := s))⟩

/-- Any two `η_c` ordered sets of cardinal `c` are order-isomorphic. -/
public theorem OrderType.type_eq_type_of_isEta {α β : Type u} [LinearOrder α] [LinearOrder β]
    (hα : IsEta #α α) (hβ : IsEta #β β) (heq : #α = #β) : type α = type β := by
  cases isEmpty_or_nonempty α with
  | inl h' =>
    have h'' : IsEmpty β := mk_eq_zero_iff.1 (heq ▸ mk_eq_zero α)
    rw [type_eq_zero.2 h', type_eq_zero.2 h'']
  | inr _ =>
    obtain ⟨r, hr, hord⟩ := Cardinal.exists_ord_eq α
    obtain ⟨s, hs, hords⟩ := Cardinal.exists_ord_eq β
    have h : IsEta #α β := heq ▸ hβ
    exact type_eq_type.2 ⟨(strictMono_f (h := h) (hord := hord) (s := s)).orderIsoOfSurjective _
      (surjective_f hα hords heq)⟩

end Order
