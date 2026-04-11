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
If α is an ordinal, and c is some cardinal, then an
η_α (c) set is a totally ordered set in which for any two subsets
X and Y of cardinality less than c, if every element of
X is less than every element of Y then there is some element
greater than all elements of X and less than all elements of
Y.
In the literature, η_α := η_α (ℵ_α), but this definition is more general.
-/

def IsEta (α : Type u) (c : Cardinal.{u}) [LinearOrder α] : Prop :=
  ∀ s t : Set α, #s < c → #t < c →
    (∀ x ∈ s, ∀ y ∈ t, x < y) → ∃ z, (∀ x ∈ s, x < z) ∧ (∀ y ∈ t, z < y)


namespace IsEta

open Order OrderType

variable {α β γ : Type u} [LinearOrder α] [LinearOrder β] [LinearOrder γ] {c c' : Cardinal.{u}}

theorem exists_between (h : IsEta α c) {s t : Set α} (hs : #s < c) (ht : #t < c)
    (hB : ∀ x ∈ s, ∀ y ∈ t, x < y) : ∃ z, (∀ x ∈ s, x < z) ∧ (∀ y ∈ t, z < y) :=
  h s t hs ht hB

theorem card_zero : IsEta α 0 := fun _ _ hs _ _ ↦
  (hs.trans_le (Cardinal.zero_le _)).false.elim

theorem le_card (h : IsEta α c) (hc : c' ≤ c) : IsEta α c' :=
  fun s t hs ht hB ↦ h s t (hs.trans_le hc) (ht.trans_le hc) hB

theorem card_one [Nonempty α] : IsEta α 1 :=
  fun s t hs ht _ ↦ by
    simp only [Cardinal.lt_one_iff, Cardinal.mk_eq_zero_iff] at hs ht
    exact ⟨‹Nonempty α›.some, by simp [Set.eq_empty_of_isEmpty], by simp [Set.eq_empty_of_isEmpty]⟩

theorem le_one (hc : c ≤ 1) [Nonempty α] : IsEta α c := le_card card_one hc

/-- If `α` is nonempty and `β` satisfies `IsEta β (#α)`, then `β` is nonempty. -/
theorem nonempty_card {α β : Type u} [LinearOrder β] (hα : Nonempty α) (h : IsEta β (#α)) :
    Nonempty β :=
  have ⟨z, _, _⟩ : ∃ (z : β), (∀ x ∈ (∅: Set β), x < z) ∧ (∀ y ∈ (∅: Set β), z < y) := by
    refine exists_between h ?_ ?_ ?_ <;> simp [pos_iff_ne_zero.2 (mk_ne_zero α)]
  ⟨z⟩

/-- The η property implies density when the cardinal is larger than 1. -/
theorem denselyOrdered_of_IsEta (hc : 1 < c) (h : IsEta α c) : DenselyOrdered α :=
  ⟨fun x y hxy ↦ by
    obtain ⟨z, hz⟩ :  ∃ z, (∀ _x ∈ ({x} :  Set α), _x < z) ∧ (∀ _y ∈ ({y} : Set α), z < _y) := by
      refine exists_between h ?_ ?_ ?_ <;> simpa
    exact ⟨z, hz.1 x rfl, hz.2 y rfl⟩ ⟩

theorem noMinOrder_of_isEta (hc : 1 < c) (h : IsEta α c) [Nonempty α] : NoMinOrder α :=
  ⟨fun x ↦
    have ⟨z, hz, hz₂⟩ : ∃ z, (∀ x ∈ (∅ :  Set α), x < z) ∧ (∀ y ∈ ({x} : Set α), z < y) := by
      refine exists_between h ?_ ?_ ?_ <;> simp [hc,lt_trans zero_lt_one hc]
    ⟨z, hz₂ x (Set.mem_singleton x)⟩⟩

theorem noMaxOrder_of_isEta (hc : 1 < c) (h : IsEta α c) [Nonempty α] : NoMaxOrder α :=
  ⟨fun x ↦
    have ⟨z, hz₁, hz₂⟩ : ∃z, (∀ _x ∈ ({x} : Set α), _x < z) ∧ ∀ y ∈ (∅ : Set α), z < y := by
      refine exists_between h  ?_ ?_ ?_ <;> simp [lt_trans zero_lt_one hc,hc]
    ⟨z, hz₁ x (Set.mem_singleton x)⟩⟩

example [IsEmpty α] : NoMaxOrder α := inferInstance

theorem noBotOrder_of_isEta (hc : 1 < c) (h : IsEta α c) [Nonempty α] : NoBotOrder α :=
  (noBotOrder_iff_noMinOrder α).2 (noMinOrder_of_isEta hc h)

theorem noTopOrder_of_isEta (hc : 1 < c) (h : IsEta α c) [Nonempty α] : NoTopOrder α :=
  ⟨fun x ↦
    have ⟨z, hz₁, _⟩ :∃z,(∀ _x ∈ ({x} : Set α), _x < z) ∧ ∀ y ∈ (∅ : Set α), z < y := by
      refine exists_between h (s := {x}) (t := ∅) ?_ ?_ ?_ <;> simp [lt_trans zero_lt_one hc, hc]
    ⟨z, not_le_of_gt (hz₁ x (Set.mem_singleton x))⟩⟩

open Classical in
/-- When `1 < c`, an `IsEta α c` linear order is nontrivial. -/
theorem nontrivial_of_isEta (hc : 1 < c) (h : IsEta α c) [Nonempty α] : Nontrivial α := by
  obtain ⟨b⟩ := ‹Nonempty α›
  obtain ⟨z, hbz, _⟩ :=
    exists_between h (s := {b}) (t := ∅) (by simpa)
    (by rw [mk_eq_zero]; exact bot_lt_iff_ne_bot.2 (ne_of_gt (lt_trans zero_lt_one hc))) (by simp)
  exact nontrivial_of_lt b z (hbz b (Set.mem_singleton b))

/-- Order-isomorphic linear orders satisfy `IsEta` for the same cardinal. -/
theorem orderIso_isEta (e : α ≃o β) : IsEta α c = IsEta β c :=
  propext <| by
    refine ⟨fun H s t hs ht hsep ↦ ?_, fun H s t hs ht hsep ↦ ?_⟩
    · obtain ⟨z, hz₁, hz₂⟩ := by
        refine H (e.symm '' s) (e.symm '' t) ?_ ?_ (fun a ⟨x, hx, ((hex: e.symm x = a))⟩ b
        ⟨y, hy, (hey : e.symm y = b)⟩ ↦ by
          simpa [e.lt_iff_lt,←hex,←hey] using hsep x hx y hy) <;>
        simpa [mk_image_eq e.symm.injective]
      refine ⟨e z, fun x hx ↦ ?_, fun y hy ↦ ?_⟩
      · grind [e.apply_symm_apply,(e.lt_iff_lt).mpr,(e.lt_iff_lt).mpr (hz₁ (e.symm x) ⟨x, hx, rfl⟩)]
      · simpa [e.apply_symm_apply] using (e.lt_iff_lt).mpr (hz₂ (e.symm y) ⟨y, hy, rfl⟩)
    · obtain ⟨z : β, hz₁ : ∀ x ∈ ⇑e '' s, x < z, hz₂ : ∀ y ∈ ⇑e '' t, z < y⟩ :=
        by refine H (e '' s) (e '' t) ?_ ?_ ?_ <;> simpa [mk_image_eq e.injective]
      refine ⟨e.symm z, fun x hx ↦ ?_, fun y hy ↦ ?_⟩
      <;> rw [← e.lt_iff_lt, e.apply_symm_apply]
      · exact hz₁ (e x) ⟨x, hx, rfl⟩
      · exact hz₂ (e y) ⟨y, hy, rfl⟩

lemma orderType_isEta_eq (h : type α = type β) : IsEta α c = IsEta β c :=
  orderIso_isEta (type_eq_type.mp h).some

/-- `IsEta` is unchanged under the order dual. -/
theorem isEta_dual : IsEta αᵒᵈ c ↔ IsEta α c := by
  refine ⟨fun H s t hs ht hB ↦ ?_, fun H s t hs ht hB ↦ ?_⟩
  <;> obtain ⟨z, hz₁, hz₂⟩ := H t s ht hs fun x hx y hy ↦ hB y hy x hx
  · exact ⟨z, fun x hx ↦ hz₂ x hx, fun y hy ↦ hz₁ y hy⟩
  · exact ⟨z, fun x hx ↦ hz₂ x hx, fun y hy ↦ hz₁ y hy⟩

theorem exists_between_finset_coe (h : IsEta α c) {s t : Finset α}
    (hs : #(s : Set α) < c) (ht : #(t : Set α) < c) (hB : ∀ x ∈ s, ∀ y ∈ t, x < y) :
    ∃ z, (∀ x ∈ s, x < z) ∧ (∀ y ∈ t, z < y) :=
  exists_between h hs ht fun x hx y hy ↦ hB x hx y hy

theorem exists_between_finset (h : IsEta α c) {s t : Finset α}
    (hs : (↑(s.card : ℕ) : Cardinal) < c) (ht : (↑(t.card : ℕ) : Cardinal) < c)
    (hB : ∀ x ∈ s, ∀ y ∈ t, x < y) :
    ∃ z, (∀ x ∈ s, x < z) ∧ (∀ y ∈ t, z < y) := by
  exact exists_between_finset_coe h (by simpa [mk_coe_finset]) (by simpa [mk_coe_finset]) hB

lemma isEta_aleph0 [Nonempty α] [DenselyOrdered α] [NoMaxOrder α] [NoMinOrder α] : IsEta α aleph0 :=
  fun s t hs ht hB ↦ by
    rw [Cardinal.lt_aleph0_iff_finite] at *
    exact Set.Finite.exists_between' hs ht hB

lemma Rat.isEta_aleph0 : IsEta ℚ aleph0 := IsEta.isEta_aleph0

variable {α β : Type u} [LinearOrder α] [LinearOrder β]

/-- Given `IsEta β (#α)` amd a countable `α` , `α` embeds into `β` with an order embedding. -/
theorem OrderType.type_le_type_of_isEta_of_countable [Countable α] (h : IsEta β (#α)) :
    type α ≤ type β := by
  rcases isEmpty_or_nonempty α with hαe | hαn
  · rw [type_eq_zero.2 hαe]
    exact OrderType.zero_le _
  rcases lt_or_ge (1 : Cardinal) (#α) with h1α | hα1
  · have hβ := nonempty_card hαn h
    have _ := denselyOrdered_of_IsEta h1α h
    haveI _ := nontrivial_of_isEta h1α h
    exact type_le_type (Order.embedding_from_countable_to_dense (α := α) (β := β)).some
  · classical
    have hβ := nonempty_card hαn h
    have hu : Subsingleton α := le_one_iff_subsingleton.1 hα1
    let b : β := Classical.choice hβ
    refine type_le_type (OrderEmbedding.ofStrictMono (fun _ : α => b) fun x y hxy ↦ ?_)
    exact False.elim (lt_irrefl x (hxy.trans_eq (hu.elim y x)))

section

variable {α β : Type*} (a : α) [LT α] {r : α → α → Prop} (g : ∀ y, r y a → β)

@[reducible]
def lo : Set β := Set.range fun (x : {x : α // r x a ∧ x < a}) ↦ g x.1 x.2.1

@[reducible]
def hi : Set β := Set.range fun (x : {x : α // r x a ∧ a < x}) ↦ g x.1 x.2.1

lemma card_subtype_le {α : Type u} {r : α → α → Prop} [IsWellOrder α r]
    {h : (#α).ord = Ordinal.type r} : ∀ a, #{ x : α // r x a } < #α :=
  fun a ↦ Cardinal.card_typein_lt a h

lemma hlo_card {α β : Type u} {r : α → α → Prop} [LT α] [IsWellOrder α r]
    (h : (#α).ord = Ordinal.type r) : ∀ a (g: ∀ y, r y a → β), #(lo (β := β) a g) < #α :=
  fun a _ ↦ Cardinal.mk_range_le.trans_lt ((Cardinal.mk_subtype_le_of_subset
    (fun _ hx ↦ hx.1)).trans_lt ((card_subtype_le (h:=h)) a))

lemma hhi_card {α β : Type u} {r : α → α → Prop} [LT α] [IsWellOrder α r]
    (h : (#α).ord = Ordinal.type r) : ∀ a (g: ∀ y, r y a → β), #(hi (β := β) a g) < #α :=
  fun a _ ↦ Cardinal.mk_range_le.trans_lt ((Cardinal.mk_subtype_le_of_subset
    (fun _ hx ↦ hx.1)).trans_lt (card_subtype_le (h:=h) a))

open Classical in
/-- The map whoch will be an order embedding between `α` and `β`. -/
@[reducible]
noncomputable def f {α β : Type u} {r : α → α → Prop} [Nonempty α] [LinearOrder α]
    [LinearOrder β] [hr : IsWellOrder α r] (h : IsEta β (#α))
    (hord : (#α).ord = Ordinal.type r) : α → β :=
  hr.wf.fix fun a g ↦ if hsep : ∀ b ∈ lo a g, ∀ c ∈ hi a g, b < c then
    (h.exists_between (hlo_card (h := hord) a g) (hhi_card hord a g) hsep).choose
  else (nonempty_card inferInstance h).some

open Classical in
private lemma f_aux {α β : Type u} (r : α → α → Prop) [Nonempty α] [LinearOrder α] [LinearOrder β]
   [hr : IsWellOrder α r] {h : IsEta β (#α)} {hord : (#α).ord = Ordinal.type r} :
   let f := h.f hord
   ∀ (a : α), f a =
   if hsep : ∀ b ∈ lo a (fun y _ ↦ f y), ∀ c ∈ hi a (fun y _ ↦ f y), b < c
   then (h.exists_between (s := (lo a fun y _ ↦ f y)) (t := hi a fun y _ ↦ f y)
      (hlo_card hord a (fun y _ ↦ f y))
      (hhi_card hord a (fun y _ ↦ f y)) hsep).choose
    else (nonempty_card inferInstance h).some :=
  fun a ↦ by
  change hr.wf.fix _ a = _
  conv_lhs => rw [WellFounded.fix_eq]

private lemma le_lo {α β : Type u} (r : α → α → Prop) [Nonempty α] [LinearOrder α] [LinearOrder β]
    [hr : IsWellOrder α r] {h : IsEta β (#α)} {hord : (#α).ord = Ordinal.type r} :
    let f := h.f hord
    ∀ (a : α) (hsep : ∀ x ∈ lo a fun y _ ↦ f y, ∀ y ∈ hi a fun y _ ↦ f y, x < y),
    ∀ x ∈ lo (r := r) a fun y _ ↦ f y, x < (exists_between h (hlo_card hord a fun y _ ↦ f y)
    (hhi_card hord a fun y _ ↦ f y) hsep).choose :=
  let f := h.f hord
  fun a hsep ↦ (h.exists_between (hlo_card hord a (fun y _ ↦ f y))
  (hhi_card hord a (fun y _ ↦ f y)) hsep).choose_spec.1

private lemma hi_le {α β : Type u} (r : α → α → Prop) [Nonempty α] [LinearOrder α] [LinearOrder β]
    [hr : IsWellOrder α r] {h : IsEta β (#α)} {hord : (#α).ord = Ordinal.type r} :
    let f := h.f hord
    ∀ (a : α) (hsep : ∀ x ∈ lo (r:=r) a fun y _ ↦ f y, ∀ y ∈ hi a fun y _ ↦ f y, x < y),
    ∀ y ∈ hi (r:= r) a fun y _ ↦ f y, (exists_between h (hlo_card hord a fun y _ ↦ f y)
    (hhi_card hord a fun y _ ↦ f y) hsep).choose < y  :=
  let f := h.f hord
  fun a hsep ↦ (h.exists_between (hlo_card hord a (fun y _ ↦ f y))
  (hhi_card hord a (fun y _ ↦ f y)) hsep).choose_spec.2

private lemma f_aux₁ {α β : Type u} (r : α → α → Prop) [Nonempty α] [LinearOrder α] [LinearOrder β]
    [hr : IsWellOrder α r] {h : IsEta β (#α)} {hord : (#α).ord = Ordinal.type r} (a : α) :
    let f := h.f hord
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

lemma strictMono_f {α β : Type u} [Nonempty α] (r : α → α → Prop) [IsWellOrder α r] [LinearOrder α]
    [LinearOrder β] {hord : (#α).ord = Ordinal.type r} {h : IsEta β (#α)} :
    StrictMono (@f _ β r _ _ _ _ h hord) := fun {x y} hxy ↦ by
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

theorem OrderType.type_le_type_of_isEta {α β : Type u} [LinearOrder α] [LinearOrder β]
    (h : IsEta β (#α)) : type α ≤ type β := by
  rcases Cardinal.exists_ord_eq α with ⟨r, hr, hord⟩
  rw [type_le_type_iff]
  by_cases hα : Nonempty α
  · exact ⟨(OrderEmbedding.ofStrictMono (h.f hord)
      (strictMono_f (h:=h) r))⟩
  · push Not at hα
    use @OrderEmbedding.ofIsEmpty α β _ _ _ |>.toEmbedding
    simp

end IsEta

end

end Order
