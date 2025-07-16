/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.Surreal.Cut

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

namespace Surreal
namespace Cut

/-! ### Birthday of cuts -/

/-- The birthday of a cut `x` is defined as the infimum of `⨆ a ∈ s, a.birthday + 1` over all
sets `s` of surreals where either the infimum of the left cuts or the supremum of right cuts of `s`
equals `x`.

The birthday takes values in `WithTop NatOrdinal`. Cuts with birthday `⊤` are exactly those that
aren't `IsSmall`.

This isn't a term in the literature, but it's useful for proving that birthdays of surreals equal
those of their associated games. -/
noncomputable def birthday (x : Cut) : WithTop NatOrdinal :=
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

@[simp]
theorem birthday_bot : birthday ⊥ = 0 := by
  simpa using birthday_sSup_rightSurreal_le ∅

@[simp]
theorem birthday_top : birthday ⊤ = 0 := by
  simpa using birthday_sInf_leftSurreal_le ∅

-- TODO: is this an equality?
theorem birthday_leftSurreal_le (x : Surreal) : (leftSurreal x).birthday ≤ x.birthday + 1 := by
  simpa using birthday_sInf_leftSurreal_le {x}

-- TODO: is this an equality?
theorem birthday_rightSurreal_le (x : Surreal) : (rightSurreal x).birthday ≤ x.birthday + 1 := by
  simpa using birthday_sSup_rightSurreal_le {x}

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

theorem exists_birthday_lt_of_mem_Ioo {x y z : Cut} (h : y ∈ Ioo x z) :
    ∃ a : Surreal


  #exit

theorem birthday_iInf_le {ι : Type*} (f : ι → Cut) : (⨅ i, f i).birthday ≤ ⨆ i, (f i).birthday := by
  obtain ⟨x, hx⟩ | hx := exists_or_forall_not (IsLeast (range f))
  · obtain ⟨i, rfl⟩ := hx.1
    convert le_iSup _ i
    exact congrArg _ hx.csInf_eq
  · simp [IsLeast, lowerBounds] at hx

theorem birthday_iSup_le {ι : Type*} (f : ι → Cut) : (⨆ i, f i).birthday ≤ ⨆ i, (f i).birthday := by
  rw [← birthday_neg, neg_iSup]
  simpa using birthday_iInf_le (fun i ↦ -f i)

theorem birthday_sInf_le (s : Set Cut) : (sInf s).birthday ≤ sSup (birthday '' s) := by
  rw [sInf_eq_iInf', sSup_image']
  exact birthday_iInf_le _

theorem birthday_sSup_le (s : Set Cut) : (sSup s).birthday ≤ sSup (birthday '' s) := by
  rw [sSup_eq_iSup', sSup_image']
  exact birthday_iSup_le _

#exit
/-! ### Small cuts -/

/-- A "small cut" is defined as either the infimum of a small set of left cuts of surreals,
or the supremum of a small set of right cuts of surreals.

Equivalently, small cuts are the closure of left and right cuts of surreals under small infima and
suprema.

This isn't a term in the literature, but it's useful for proving that birthdays of surreals equal
those of their associated games. -/
class inductive IsSmall : Cut.{u} → Prop
  | sInf' (s : Set Surreal) [Small.{u} s] : (sInf (leftSurreal '' s)).IsSmall
  | sSup' (s : Set Surreal) [Small.{u} s] : (sSup (rightSurreal '' s)).IsSmall

namespace IsSmall

theorem iInf' {ι : Type*} [Small.{u} ι] (f : ι → Surreal.{u}) :
    (⨅ i, leftSurreal (f i)).IsSmall := by
  rw [iInf, range_comp']
  exact .sInf' _

theorem iSup' {ι : Type*} [Small.{u} ι] (f : ι → Surreal.{u}) :
    (⨆ i, rightSurreal (f i)).IsSmall := by
  rw [iSup, range_comp']
  exact .sSup' _

protected instance neg (x : Cut) [hx : x.IsSmall] : (-x).IsSmall := by
  cases hx with
  | sInf' s => simpa using .sSup' (-s)
  | sSup' s => simpa using .sInf' (-s)

@[simp]
theorem neg_iff {x : Cut} : IsSmall (-x) ↔ IsSmall x := by
  refine ⟨?_, @IsSmall.neg x⟩
  convert @IsSmall.neg (-x)
  rw [neg_neg]

protected instance bot : IsSmall ⊥ := by
  simpa using IsSmall.sSup' ∅

protected instance top : IsSmall ⊤ := by
  simpa using IsSmall.sInf' ∅

@[simp]
protected instance leftSurreal (x : Surreal) : (leftSurreal x).IsSmall := by
  simpa using IsSmall.sInf' {x}

@[simp]
protected instance rightSurreal (x : Surreal) : (rightSurreal x).IsSmall := by
  simpa using IsSmall.sSup' {x}

theorem birthday_lt_top_iff {x : Cut.{u}} : x.birthday < ⊤ ↔ x.IsSmall := by
  refine ⟨fun hx ↦ ?_, ?_⟩
  · obtain ⟨o, ho⟩ := WithTop.ne_top_iff_exists.1 hx.ne
    obtain ⟨s, rfl | rfl, hs⟩ := birthday_eq_sSup_birthday x
    all_goals
      suffices Small.{u} s by first | exact .sInf' _ | exact .sSup' _
      refine small_subset (s := {x : Surreal | x.birthday < o}) fun x hx ↦ ?_
      rw [← hs] at ho
      rw [mem_setOf, ← WithTop.coe_lt_coe, ho, lt_sSup_iff]
      refine ⟨x.birthday + 1, ⟨?_, ?_⟩⟩
      · use x
      · convert WithTop.coe_lt_coe.2 <| Order.lt_succ x.birthday
        simp [Order.succ_eq_add_one]
  · rintro (s | s)
    · exact (birthday_sInf_leftSurreal_le' s).trans_lt (WithTop.coe_lt_top _)
    · exact (birthday_sSup_rightSurreal_le' s).trans_lt (WithTop.coe_lt_top _)

theorem birthday_lt_top (x : Cut) [hx : IsSmall x] : x.birthday < ⊤ :=
  birthday_lt_top_iff.2 hx

protected instance iInf {ι : Type*} {f : ι → Cut.{u}} [Small.{u} ι] [H : ∀ i, IsSmall (f i)] :
    IsSmall (⨅ i, f i) := by
  simp_rw [← birthday_lt_top_iff] at *
  choose g hg using fun i ↦ WithTop.ne_top_iff_exists.1 (H i).ne
  apply (birthday_iInf_le _).trans_lt
  simp_rw [← hg, ← WithTop.coe_iSup _ (NatOrdinal.bddAbove_of_small _)]
  exact WithTop.coe_lt_top _

protected instance iSup {ι : Type*} {f : ι → Cut.{u}} [Small.{u} ι] [∀ i, IsSmall (f i)] :
    (⨆ i, f i).IsSmall := by
  rw [← IsSmall.neg_iff, neg_iSup]
  infer_instance

protected theorem sInf {s : Set Cut.{u}} [Small.{u} s] (H : ∀ x ∈ s, IsSmall x) :
    (sInf s).IsSmall := by
  rw [sInf_eq_iInf']
  rw [Subtype.forall'] at H
  infer_instance

protected theorem sSup {s : Set Cut.{u}} [Small.{u} s] (H : ∀ x ∈ s, IsSmall x) :
    (sSup s).IsSmall := by
  rw [sSup_eq_iSup']
  rw [Subtype.forall'] at H
  infer_instance

private theorem game (x : IGame) : IsSmall (leftGame (.mk x)) ∧ IsSmall (rightGame (.mk x)) := by
  obtain h | h := lt_or_ge (supLeft x) (infRight x)
  · rw [← simplestBtwn_supLeft_infRight h]
    simp
  · rw [leftGame_eq_supLeft_of_le h, rightGame_eq_infRight_of_le h,
      supLeft, infRight, iSup_subtype', iInf_subtype']
    exact ⟨@IsSmall.iSup _ _ _ fun _ ↦ (game _).2, @IsSmall.iInf _ _ _ fun _ ↦ (game _).1⟩
termination_by x
decreasing_by igame_wf

protected instance leftGame (x : Game) : IsSmall (leftGame x) := by
  simpa using (game x.out).1

protected instance rightGame (x : Game) : IsSmall (rightGame x) := by
  simpa using (game x.out).2

protected instance supLeft (x : IGame) : IsSmall (supLeft x) := by
  rw [supLeft, iSup_subtype']
  infer_instance

protected instance infRight (x : IGame) : IsSmall (infRight x) := by
  rw [infRight, iInf_subtype']
  infer_instance

end IsSmall

end Cut
end Surreal
