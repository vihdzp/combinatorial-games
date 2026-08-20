/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Aaron Liu
-/
module

public import CombinatorialGames.Surreal.Cut

import CombinatorialGames.Mathlib.WithTop

/-!
# Birthday of cuts

We introduce the birthday of a (surreal) cut as `Cut.birthday`, and relate it to the birthdays of
games and surreal numbers.

This definition doesn't exist in the literature, but it's useful in proving results about the
birthdays of games. In particular, it allows us to prove the equality
`birthday_toGame : x.toGame.birthday = x.birthday` for surreal numbers `x`. See
https://mathoverflow.net/a/497645/147705 for a "plaintext" version of this proof.
-/

universe u

open Set

public noncomputable section

section ForMathlib

theorem WithTop.isSuccPrelimit_coe_iff {α : Type*} [Preorder α] {x : α} :
    Order.IsSuccPrelimit (WithTop.some x) ↔ Order.IsSuccPrelimit x := by
  simp [Order.IsSuccPrelimit, WithTop.forall]

theorem Set.forall_mem_iUnion {α : Type*} {ι : Sort*} {p : α → Prop} {f : ι → Set α} :
    (∀ x ∈ ⋃ i, f i, p x) ↔ (∀ i, ∀ x ∈ f i, p x) := by
  simp_rw [mem_iUnion, forall_exists_index]
  apply forall_comm

end ForMathlib

namespace Surreal.Cut

/-! ### Birthday of cuts -/

/-- The birthday of a cut `x` is defined as the infimum of `⨆ a ∈ s, a.birthday + 1` over all
sets `s` of surreals where either the infimum of the left cuts or the supremum of right cuts of `s`
equals `x`.

The birthday takes values in `WithTop NatOrdinal`. Cuts with birthday `⊤` are precisely those where
the set `s` is not small.

This isn't a term in the literature, but it's useful for proving that birthdays of surreals equal
those of their associated games. -/
def birthday (x : Cut) : WithTop NatOrdinal :=
  sInf <| (fun s ↦ sSup ((fun x ↦ x.birthday + 1) '' s)) ''
     {s : Set Surreal | sInf (leftSurreal '' s) = x ∨ sSup (rightSurreal '' s) = x}

theorem birthday_eq_sSup_birthday (x : Cut) :
    ∃ s : Set Surreal, (sInf (leftSurreal '' s) = x ∨ sSup (rightSurreal '' s) = x) ∧
      sSup ((fun x ↦ (x.birthday : WithTop _) + 1) '' s) = birthday x :=
  csInf_mem (image_nonempty.2 ⟨_, .inr <| sSup_rightSurreal_left x⟩)

theorem birthday_sInf_leftSurreal_le (s : Set Surreal) :
    (sInf (leftSurreal '' s)).birthday ≤
      sSup ((fun x ↦ (x.birthday : WithTop _) + 1) '' s)  :=
  csInf_le' ⟨s, by simp⟩

theorem birthday_sSup_rightSurreal_le (s : Set Surreal) :
    (sSup (rightSurreal '' s)).birthday ≤
      (sSup ((fun x ↦ (x.birthday : WithTop _) + 1) '' s)) :=
  csInf_le' ⟨s, by simp⟩

theorem birthday_iInf_leftSurreal_le {ι : Type*} (f : ι → Surreal) :
    (⨅ i, leftSurreal (f i)).birthday ≤ ⨆ i, ((f i).birthday : WithTop _) + 1 := by
  convert birthday_sInf_leftSurreal_le (range f) <;>
  simp [iInf, iSup, ← range_comp']

theorem birthday_iSup_rightSurreal_le {ι : Type*} (f : ι → Surreal) :
    (⨆ i, rightSurreal (f i)).birthday ≤ ⨆ i, ((f i).birthday : WithTop _) + 1 := by
  convert birthday_sSup_rightSurreal_le (range f) <;>
  simp [iSup, ← range_comp']

theorem birthday_sInf_leftSurreal_le' (s : Set Surreal.{u}) [Small.{u} s] :
    (sInf (leftSurreal '' s)).birthday ≤
      (sSup ((fun x ↦ x.birthday + 1) '' s) : NatOrdinal) := by
  apply (birthday_sInf_leftSurreal_le s).trans_eq
  rw [WithTop.coe_sSup' (NatOrdinal.bddAbove_of_small _)]
  simp [image_image]

theorem birthday_sSup_rightSurreal_le' (s : Set Surreal.{u}) [Small.{u} s] :
    (sSup (rightSurreal '' s)).birthday ≤
      (sSup ((fun x ↦ x.birthday + 1) '' s) : NatOrdinal) := by
  apply (birthday_sSup_rightSurreal_le s).trans_eq
  rw [WithTop.coe_sSup' (NatOrdinal.bddAbove_of_small _)]
  simp [image_image]

theorem birthday_iInf_leftSurreal_le' {ι : Type*} (f : ι → Surreal.{u}) [Small.{u} ι] :
    (⨅ i, leftSurreal (f i)).birthday ≤ ⨆ i, (f i).birthday + 1 := by
  convert birthday_sInf_leftSurreal_le' (range f) <;>
  simp [iInf, iSup, ← range_comp']

theorem birthday_iSup_rightSurreal_le' {ι : Type*} (f : ι → Surreal.{u}) [Small.{u} ι] :
    (⨆ i, rightSurreal (f i)).birthday ≤ ⨆ i, (f i).birthday + 1 := by
  convert birthday_sSup_rightSurreal_le' (range f) <;>
  simp [iSup, ← range_comp']

theorem birthday_lt_sSup_birthday {a : Surreal} {s : Set Surreal} (ha : a ∈ s) :
    a.birthday < sSup ((fun x : Surreal ↦ (x.birthday : WithTop NatOrdinal) + 1) '' s) := by
  rw [lt_sSup_iff]
  refine ⟨a.birthday + 1, ?_, ?_⟩
  · use a
  · exact WithTop.coe_lt_coe.2 <| lt_add_one a.birthday

theorem sSup_birthday_lt_top_iff {s : Set Surreal.{u}} :
    sSup ((fun x : Surreal ↦ (x.birthday : WithTop NatOrdinal) + 1) '' s) < ⊤ ↔ Small.{u} s := by
  refine ⟨fun hs ↦ ?_, fun _ ↦ NatOrdinal.withTop_sSup_lt_top.2 <| by simp⟩
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hs.ne
  refine small_subset (s := {x : Surreal | x.birthday < a}) fun x hx ↦ ?_
  rw [mem_ofPred, ← WithTop.coe_lt_coe, ha]
  exact birthday_lt_sSup_birthday hx

theorem sSup_birthday_eq_top_iff {s : Set Surreal.{u}} :
    sSup ((fun x : Surreal ↦ (x.birthday : WithTop NatOrdinal) + 1) '' s) = ⊤ ↔ ¬ Small.{u} s := by
  simpa using sSup_birthday_lt_top_iff.not

@[simp]
theorem birthday_bot : birthday ⊥ = 0 := by
  simpa using birthday_sSup_rightSurreal_le ∅

@[simp]
theorem birthday_top : birthday ⊤ = 0 := by
  simpa using birthday_sInf_leftSurreal_le ∅

private theorem birthday_neg_le (x : Cut) : (-x).birthday ≤ x.birthday := by
  obtain ⟨x, rfl | rfl, hx⟩ := birthday_eq_sSup_birthday x
  · rw [← hx, neg_sInf, neg_leftSurreal_image]
    convert ← birthday_sSup_rightSurreal_le _ using 2
    apply image_neg_of_apply_neg_eq
    simp
  · rw [← hx, neg_sSup, neg_rightSurreal_image]
    convert ← birthday_sInf_leftSurreal_le _ using 2
    apply image_neg_of_apply_neg_eq
    simp

@[simp]
theorem birthday_neg (x : Cut) : (-x).birthday = x.birthday := by
  apply (birthday_neg_le x).antisymm
  simpa using birthday_neg_le (-x)

@[simp]
theorem birthday_leftSurreal (x : Surreal) : (leftSurreal x).birthday = x.birthday + 1 := by
  apply le_antisymm
  · simpa using birthday_sInf_leftSurreal_le {x}
  · by_contra! hx
    obtain ⟨y, hy | hy, hy'⟩ := birthday_eq_sSup_birthday (leftSurreal x)
    · have := leftSurreal_mem_of_sInf_eq hy
      simp_rw [mem_image, EmbeddingLike.apply_eq_iff_eq, exists_eq_right] at this
      apply (Order.add_one_le_of_lt <| birthday_lt_sSup_birthday this).not_gt
      rwa [hy']
    · rw [← hy', ← WithTop.coe_add_one] at hx
      have := sSup_birthday_lt_top_iff.1 (hx.trans (WithTop.coe_lt_top _))
      simpa using leftSurreal_mem_of_sSup_eq hy

@[simp]
theorem birthday_rightSurreal (x : Surreal) : (rightSurreal x).birthday = x.birthday + 1 := by
  simpa [← neg_rightSurreal] using birthday_leftSurreal (-x)

theorem birthday_of_numeric (x : Cut) [hx : x.Numeric] : x.birthday = x.toSurreal.birthday + 1 := by
  cases hx <;> simp

theorem exists_birthday_lt_of_mem_Ioo {x y z : Cut} (h : y ∈ Ioo x z) :
    ∃ a : Surreal, a.birthday < y.birthday ∧ Fits a x z := by
  obtain ⟨y, rfl | rfl, hy⟩ := birthday_eq_sSup_birthday y
  · have hz := h.2
    simp_rw [sInf_lt_iff, mem_image, exists_exists_and_eq_and, leftSurreal_lt_iff] at hz
    obtain ⟨a, ⟨hay, haz⟩⟩ := hz
    refine ⟨a, hy ▸ birthday_lt_sSup_birthday hay, ⟨?_, haz⟩⟩
    rw [← le_leftSurreal_iff]
    apply h.1.le.trans
    aesop
  · have hz := h.1
    simp_rw [lt_sSup_iff, mem_image, exists_exists_and_eq_and, lt_rightSurreal_iff] at hz
    obtain ⟨a, ⟨hay, hax⟩⟩ := hz
    refine ⟨a, hy ▸ birthday_lt_sSup_birthday hay, ⟨hax, ?_⟩⟩
    rw [← rightSurreal_le_iff]
    apply h.2.le.trans'
    aesop

theorem birthday_iInf_le {ι : Type*} (f : ι → Cut) : (⨅ i, f i).birthday ≤ ⨆ i, (f i).birthday := by
  obtain ⟨x, hx⟩ | hx := exists_or_forall_not (IsLeast (range f))
  · obtain ⟨i, rfl⟩ := hx.1
    convert le_iSup _ i
    exact congrArg _ hx.csInf_eq
  · have : ∀ i, ∃ j, f j < f i := by simpa [IsLeast, lowerBounds] using hx
    choose g hg using this
    have (i : ι) : f (g i) ∈ Ioo (iInf f) (f i) := ⟨(hg _).trans_le' (iInf_le ..), hg i⟩
    choose t ht using fun i ↦ exists_birthday_lt_of_mem_Ioo (this i)
    trans (⨅ i, leftSurreal (t i)).birthday
    · apply (congrArg ..).le
      apply le_antisymm <;> rw [le_iInf_iff] <;> intro i
      · exact (ht i).2.le_leftSurreal
      · exact iInf_le_of_le i <| (leftSurreal_lt_rightSurreal _).le.trans (ht i).2.rightSurreal_le
    · apply (birthday_iInf_leftSurreal_le _).trans
      rw [iSup_le_iff]
      exact fun i ↦ (Order.add_one_le_of_lt (ht i).1).trans (le_iSup (birthday ∘ f) _)

theorem birthday_iSup_le {ι : Type*} (f : ι → Cut) : (⨆ i, f i).birthday ≤ ⨆ i, (f i).birthday := by
  rw [← birthday_neg, neg_iSup]
  simpa using birthday_iInf_le (fun i ↦ -f i)

theorem birthday_sInf_le (s : Set Cut) : (sInf s).birthday ≤ sSup (birthday '' s) := by
  rw [sInf_eq_iInf', sSup_image']
  exact birthday_iInf_le _

theorem birthday_sSup_le (s : Set Cut) : (sSup s).birthday ≤ sSup (birthday '' s) := by
  rw [sSup_eq_iSup', sSup_image']
  exact birthday_iSup_le _

theorem birthday_simplestBtwn_le {x y : Cut.{u}} (h : x < y) :
    (simplestBtwn h).birthday ≤ max x.birthday y.birthday := by
  obtain ⟨s, rfl | rfl, hx⟩ := birthday_eq_sSup_birthday x
  · simp_rw [sInf_lt_iff, mem_image, exists_exists_and_eq_and, leftSurreal_lt_iff] at h
    obtain ⟨a, ha, hay⟩ := h
    apply (WithTop.coe_le_coe.2 <| birthday_simplestBtwn_le_of_fits _).trans
    · exact le_max_of_le_left (hx ▸ (birthday_lt_sSup_birthday ha).le)
    · refine ⟨?_, hay⟩
      aesop
  obtain ⟨t, rfl | rfl, hy⟩ := birthday_eq_sSup_birthday y; swap
  · simp_rw [lt_sSup_iff, mem_image, exists_exists_and_eq_and, lt_rightSurreal_iff] at h
    obtain ⟨a, ha, hay⟩ := h
    apply (WithTop.coe_le_coe.2 <| birthday_simplestBtwn_le_of_fits _).trans
    · exact le_max_of_le_right (hy ▸ (birthday_lt_sSup_birthday ha).le)
    · refine ⟨hay, ?_⟩
      aesop
  rw [← hx, ← hy]
  by_cases hs : Small.{u} s; swap
  · rw [← sSup_birthday_eq_top_iff] at hs
    simp [hs]
  by_cases ht : Small.{u} t; swap
  · rw [← sSup_birthday_eq_top_iff] at ht
    simp [ht]
  have H : ∀ x ∈ s, ∀ y ∈ t, x < y := by
    intro x hx y hy
    have H₁ := le_sSup (mem_image_of_mem rightSurreal hx)
    have H₂ := sInf_le (mem_image_of_mem leftSurreal hy)
    simpa using (H₁.trans_lt h).trans_le H₂
  trans (!{s | t}.birthday : WithTop NatOrdinal)
  · rw [WithTop.coe_le_coe]
    apply birthday_simplestBtwn_le_of_fits
    unfold Fits
    aesop
  · apply (WithTop.coe_le_coe.2 <| birthday_ofSets_le ..).trans_eq
    simp [Order.succ_eq_add_one, WithTop.coe_sSup' (NatOrdinal.bddAbove_of_small _), image_image]

private theorem birthday_game_le (x : IGame) :
    (supLeft x).birthday ≤ x.birthday ∧ (infRight x).birthday ≤ x.birthday ∧
    (leftGame (.mk x)).birthday ≤ x.birthday + 1 ∧
    (rightGame (.mk x)).birthday ≤ x.birthday + 1 := by
  have H₁ : (supLeft x).birthday ≤ x.birthday := by
    rw [supLeft, iSup_subtype']
    apply (birthday_iSup_le _).trans <| iSup_le fun i ↦ (birthday_game_le _).2.2.2.trans ?_
    rw [← WithTop.coe_add_one, WithTop.coe_le_coe, Order.add_one_le_iff]
    exact IGame.birthday_lt_of_mem_moves i.2
  have H₂ : (infRight x).birthday ≤ x.birthday := by
    rw [infRight, iInf_subtype']
    apply (birthday_iInf_le _).trans <| iSup_le fun i ↦ (birthday_game_le _).2.2.1.trans ?_
    rw [← WithTop.coe_add_one, WithTop.coe_le_coe, Order.add_one_le_iff]
    exact IGame.birthday_lt_of_mem_moves i.2
  use H₁, H₂
  obtain h | h := lt_or_ge (supLeft x) (infRight x)
  · rw [← simplestBtwn_supLeft_infRight h, leftGame_toGame, rightGame_toGame]
    constructor <;>
      simpa using add_le_add_left ((birthday_simplestBtwn_le h).trans (max_le H₁ H₂)) _
  · rw [leftGame_eq_supLeft_of_le h, rightGame_eq_infRight_of_le h]
    refine ⟨H₁.trans ?_, H₂.trans ?_⟩ <;>
      exact (WithTop.coe_lt_coe.2 <| Order.lt_add_one_iff.2 le_rfl).le
termination_by x
decreasing_by igame_wf

theorem birthday_supLeft_le (x : IGame) : (supLeft x).birthday ≤ x.birthday :=
  (birthday_game_le x).1

theorem birthday_infRight_le (x : IGame) : (infRight x).birthday ≤ x.birthday :=
  (birthday_game_le x).2.1

theorem birthday_leftGame_le (x : Game) : (leftGame x).birthday ≤ x.birthday + 1 := by
  obtain ⟨x, rfl, hx⟩ := x.birthday_eq_iGameBirthday
  apply (birthday_game_le x).2.2.1.trans
  rw [hx]

theorem birthday_rightGame_le (x : Game) : (rightGame x).birthday ≤ x.birthday + 1 := by
  obtain ⟨x, rfl, hx⟩ := x.birthday_eq_iGameBirthday
  apply (birthday_game_le x).2.2.2.trans
  rw [hx]

/-- The smallest birthday among *numeric* games equivalent to a surreal, is also the smallest
birthday among *all* games in general. -/
@[simp]
theorem _root_.Surreal.birthday_toGame (x : Surreal) : x.toGame.birthday = x.birthday := by
  apply (birthday_toGame_le x).antisymm
  obtain ⟨y, hy, hy'⟩ := (toGame x).birthday_eq_iGameBirthday
  have he : y ≈ x.out := by rw [← Game.mk_eq_mk]; simpa
  have hsi := supLeft_lt_infRight_of_equiv_numeric he
  have hs := simplestBtwn_supLeft_infRight hsi
  rw [hy, toGame_inj] at hs
  rw [← WithTop.coe_le_coe]
  exact (hs ▸ birthday_simplestBtwn_le hsi).trans <|
    hy' ▸ max_le (birthday_supLeft_le y) (birthday_infRight_le y)

theorem numeric_iff_birthday {x : Cut} : x.Numeric ↔ ¬Order.IsSuccPrelimit x.birthday := by
  constructor
  · rintro (_ | _) <;>
      · simp only [birthday_leftSurreal, birthday_rightSurreal]
        rw [← WithTop.coe_add_one, WithTop.isSuccPrelimit_coe_iff]
        exact Order.not_isSuccPrelimit_add_one _
  · intro h
    rw [Order.not_isSuccPrelimit_iff] at h
    obtain ⟨b, hb⟩ := h
    cases b with | top => simp at hb | coe b
    obtain ⟨s, hx | hx, hsb⟩ := birthday_eq_sSup_birthday x
    · by_cases! hs : ∃ u ∈ s, ∀ v ∈ s, u ≤ v
      · obtain ⟨u, hus, hu⟩ := hs
        have hxu : x = leftSurreal u := by
          apply le_antisymm
          · rw [← hx]
            apply sInf_le
            exact Set.mem_image_of_mem leftSurreal hus
          · rw [← hx, le_sInf_iff, Set.forall_mem_image]
            intro v hv
            rw [le_leftSurreal_iff, mem_right_leftSurreal]
            exact hu v hv
        rw [hxu]
        constructor
      · have hbs := Order.succ_eq_of_covBy hb
        rw [Order.succ_eq_add_one, ← WithTop.coe_add_one, ← hsb] at hbs
        have he (v : Surreal) (hv : v ∈ s) : ∃ c, c ≤ v ∧ c.birthday < b ∧ ∃ w ∈ s, w ≤ c := by
          obtain ⟨w, hws, hwv⟩ := hs v hv
          have hvb := birthday_lt_sSup_birthday hv
          have hwb := birthday_lt_sSup_birthday hws
          rw [← hbs, WithTop.coe_lt_coe, Order.lt_add_one_iff] at hvb hwb
          obtain hvb | hvb := hvb.eq_or_lt
          · obtain hwb | hwb := hwb.eq_or_lt
            · exact ⟨!{{w} | {v}}, (ofSets_lt_of_mem_right (by simp)).le,
                birthday_ofSets_singleton_lt_of_birthday_eq hwb hvb hwv,
                w, hws, (lt_ofSets_of_mem_left (by simp)).le⟩
            · exact ⟨w, hwv.le, hwb, w, hws, le_rfl⟩
          · exact ⟨v, le_rfl, hvb, v, hv, le_rfl⟩
        choose vv hvv hvb hvw using he
        have hxv : x = sInf (leftSurreal '' ⋃ v, Set.range (vv v)) := by
          apply le_antisymm
          · simp_rw [le_sInf_iff, forall_mem_image, Set.forall_mem_iUnion, Set.forall_mem_range]
            intro v hv
            obtain ⟨w, hws, hwv⟩ := hvw v hv
            rw [← hx]
            refine sInf_le_of_le ?_ (leftSurreal_strictMono.monotone hwv)
            exact mem_image_of_mem leftSurreal hws
          · rw [← hx, le_sInf_iff, Set.forall_mem_image]
            intro v hv
            refine sInf_le_of_le ?_ (leftSurreal_strictMono.monotone (hvv v hv))
            apply mem_image_of_mem
            apply mem_iUnion_of_mem
            apply mem_range_self
        absurd hb.lt.not_ge
        grw [hxv, birthday_sInf_le]
        simp_rw [sSup_le_iff, Set.forall_mem_image, Set.forall_mem_iUnion, Set.forall_mem_range]
        intro v hv
        rw [birthday_leftSurreal, ← WithTop.coe_add_one, WithTop.coe_le_coe, Order.add_one_le_iff]
        apply hvb
    · by_cases! hs : ∃ u ∈ s, ∀ v ∈ s, v ≤ u
      · obtain ⟨u, hus, hu⟩ := hs
        have hxu : x = rightSurreal u := by
          apply le_antisymm
          · rw [← hx, sSup_le_iff, Set.forall_mem_image]
            intro v hv
            rw [rightSurreal_le_iff, mem_left_rightSurreal]
            exact hu v hv
          · rw [← hx]
            apply le_sSup
            exact Set.mem_image_of_mem rightSurreal hus
        rw [hxu]
        constructor
      · have hbs := Order.succ_eq_of_covBy hb
        rw [Order.succ_eq_add_one, ← WithTop.coe_add_one, ← hsb] at hbs
        have he (v : Surreal) (hv : v ∈ s) : ∃ c, v ≤ c ∧ c.birthday < b ∧ ∃ w ∈ s, c ≤ w := by
          obtain ⟨w, hws, hvw⟩ := hs v hv
          have hvb := birthday_lt_sSup_birthday hv
          have hwb := birthday_lt_sSup_birthday hws
          rw [← hbs, WithTop.coe_lt_coe, Order.lt_add_one_iff] at hvb hwb
          obtain hvb | hvb := hvb.eq_or_lt
          · obtain hwb | hwb := hwb.eq_or_lt
            · exact ⟨!{{v} | {w}}, (lt_ofSets_of_mem_left (by simp)).le,
                birthday_ofSets_singleton_lt_of_birthday_eq hvb hwb hvw,
                w, hws, (ofSets_lt_of_mem_right (by simp)).le⟩
            · exact ⟨w, hvw.le, hwb, w, hws, le_rfl⟩
          · exact ⟨v, le_rfl, hvb, v, hv, le_rfl⟩
        choose vv hvv hvb hvw using he
        have hxv : x = sSup (rightSurreal '' ⋃ v, Set.range (vv v)) := by
          apply le_antisymm
          · rw [← hx, sSup_le_iff, Set.forall_mem_image]
            intro v hv
            refine le_sSup_of_le ?_ (rightSurreal_strictMono.monotone (hvv v hv))
            apply mem_image_of_mem
            apply mem_iUnion_of_mem
            apply mem_range_self
          · simp_rw [sSup_le_iff, forall_mem_image, Set.forall_mem_iUnion, Set.forall_mem_range]
            intro v hv
            obtain ⟨w, hws, hvw⟩ := hvw v hv
            rw [← hx]
            refine le_sSup_of_le ?_ (rightSurreal_strictMono.monotone hvw)
            exact mem_image_of_mem rightSurreal hws
        absurd hb.lt.not_ge
        grw [hxv, birthday_sSup_le]
        simp_rw [sSup_le_iff, Set.forall_mem_image, Set.forall_mem_iUnion, Set.forall_mem_range]
        intro v hv
        rw [birthday_rightSurreal, ← WithTop.coe_add_one, WithTop.coe_le_coe, Order.add_one_le_iff]
        apply hvb

end Surreal.Cut
end
