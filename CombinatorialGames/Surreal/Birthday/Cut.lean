import CombinatorialGames.Surreal.Cut

/-!
# Birthday of cuts

We introduce the birthday of a (surreal) cut as `Cut.birthday`, and relate it to the birthdays of
games and surreal numbers.

In particular, we're able to prove the equality `birthday_toGame : x.toGame.birthday = x.birthday`
for a surreal number `x`.
-/

namespace Surreal.Cut

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
  rw [WithTop.coe_sSup']
  · simp [image_image]
  · exact Ordinal.bddAbove_of_small _

theorem birthday_sSup_rightSurreal_le' (s : Set Surreal.{u}) [Small.{u} s] :
    (sSup (rightSurreal '' s)).birthday ≤
      (sSup ((fun x ↦ x.birthday + 1) '' s) : NatOrdinal) := by
  apply (birthday_sSup_rightSurreal_le s).trans_eq
  rw [WithTop.coe_sSup']
  · simp [image_image]
  · exact Ordinal.bddAbove_of_small _

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
