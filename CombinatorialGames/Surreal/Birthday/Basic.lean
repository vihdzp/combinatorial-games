/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
import CombinatorialGames.Game.Birthday
import CombinatorialGames.Surreal.Ordinal


/-!
# Birthdays of surreals

We define the birthday of a surreal number as the smallest birthday of all numeric pre-games
equivalent to it.

The numeric condition can be removed to yield an equivalent definition, but that is proved in
`CombinatorialGames.Surreal.Birthday.Cut`.
-/

universe u
noncomputable section

namespace Surreal
open IGame NatOrdinal Order Set

/-- The birthday of a surreal number is defined as the least birthday
among all *numeric* pre-games that define it.

The numeric condition can be removed, see `Surreal.birthday_toGame`. -/
def birthday (x : Surreal.{u}) : NatOrdinal.{u} :=
  sInf (IGame.birthday '' {c | ∃ _ : Numeric c, mk c = x})

/-! ### Basic properties -/

theorem birthday_eq_iGameBirthday (x : Surreal) :
    ∃ (y : IGame) (_ : Numeric y), mk y = x ∧ y.birthday = birthday x := by
  simp_rw [exists_and_right]
  refine csInf_mem (image_nonempty.2 ?_)
  exact ⟨_, _, x.out_eq⟩

theorem birthday_mk_le (x : IGame) [Numeric x] : birthday (mk x) ≤ x.birthday :=
  csInf_le' ⟨x, ⟨_, rfl⟩, rfl⟩

@[simp]
theorem birthday_zero : birthday 0 = 0 := by
  simpa using birthday_mk_le 0

@[simp]
theorem birthday_eq_zero {x : Surreal} : birthday x = 0 ↔ x = 0 := by
  obtain ⟨_, _, _, _⟩ := birthday_eq_iGameBirthday x
  refine ⟨fun _ ↦ ?_, ?_⟩ <;> simp_all

private theorem birthday_neg_le (x : Surreal) : (-x).birthday ≤ x.birthday := by
  obtain ⟨y, _, rfl, hy⟩ := birthday_eq_iGameBirthday x
  rw [← hy, ← IGame.birthday_neg]
  exact birthday_mk_le _

@[simp]
theorem birthday_neg (x : Surreal) : (-x).birthday = x.birthday := by
  apply (birthday_neg_le x).antisymm
  simpa using birthday_neg_le (-x)

theorem le_toSurreal_birthday (x : Surreal) : x ≤ x.birthday.toSurreal := by
  obtain ⟨y, _, rfl, hy⟩ := birthday_eq_iGameBirthday x
  rw [← hy]
  exact y.le_toIGame_birthday

theorem neg_toSurreal_birthday_le (x : Surreal) : -x.birthday.toSurreal ≤ x := by
  simpa [neg_le] using le_toSurreal_birthday (-x)

@[simp]
theorem birthday_toSurreal (o : NatOrdinal) : birthday o.toSurreal = o := by
  apply le_antisymm
  · simpa using birthday_mk_le o.toIGame
  · simpa using o.toSurreal.le_toSurreal_birthday

@[simp, norm_cast]
theorem birthday_natCast (n : ℕ) : birthday n = n := by
  simpa using birthday_toSurreal n

@[simp]
theorem birthday_ofNat (n : ℕ) [n.AtLeastTwo] : birthday ofNat(n) = n :=
  birthday_natCast n

@[simp]
theorem birthday_one : birthday 1 = 1 := by
  simpa using birthday_natCast 1

theorem birthday_eq_iInf_fits (x : IGame) [hx : Numeric x] :
    birthday (.mk x) = ⨅ y : {y : Subtype Numeric // Fits y x}, birthday (.mk y.1.1) := by
  let f (y : {y : Subtype Numeric // Fits y x}) := birthday (.mk y.1)
  let : Inhabited {y : Subtype Numeric // Fits y x} := ⟨⟨x, hx⟩, Fits.refl _⟩
  apply (ciInf_le' f default).antisymm'
  obtain ⟨⟨⟨y, _⟩, hy⟩, hy'⟩ := ciInf_mem f
  obtain ⟨z, _, hz, hz'⟩ := birthday_eq_iGameBirthday (.mk y)
  rw [← hz'.trans hy']
  apply (birthday_mk_le z).trans'
  congr! 1
  rw [eq_comm, mk_eq_mk] at hz ⊢
  refine (hy.congr hz).equiv_of_forall_birthday_le fun w hw hw' ↦ hz' ▸ ?_
  exact hy'.trans_le <| (ciInf_le' f ⟨⟨w, hw⟩, hw'⟩).trans (birthday_mk_le _)

-- TODO: can we remove the `Numeric x` assumption?
theorem _root_.IGame.Fits.birthday_le {x y : IGame} [hx : Numeric x] [Numeric y] (h : Fits x y) :
    birthday (.mk y) ≤ birthday (.mk x) := by
  let f (x : {x : Subtype Numeric // Fits x y}) := birthday (.mk x.1)
  rw [birthday_eq_iInf_fits y]
  exact ciInf_le' f ⟨⟨x, hx⟩, h⟩

-- TODO: can we remove the `Numeric x` assumption?
theorem _root_.IGame.Fits.birthday_lt {x y : IGame} [Numeric x] [Numeric y]
    (h : Fits x y) (he : ¬ x ≈ y) : birthday (.mk y) < birthday (.mk x) := by
  apply h.birthday_le.lt_of_not_ge
  contrapose he
  obtain ⟨z, _, hz, hz'⟩ := birthday_eq_iGameBirthday (.mk x)
  rw [← hz'] at he
  rw [eq_comm, mk_eq_mk] at hz
  exact hz.trans <| (h.congr hz).equiv_of_forall_birthday_le fun w _ hw ↦
    he.trans (hw.birthday_le.trans <| birthday_mk_le _)

theorem birthday_ofSets_le {s t : Set Surreal.{u}}
    [Small.{u} s] [Small.{u} t] {H : ∀ x ∈ s, ∀ y ∈ t, x < y} :
    !{s | t}.birthday ≤ max (sSup (succ ∘ birthday '' s)) (sSup (succ ∘ birthday '' t)) := by
  choose f hf using birthday_eq_iGameBirthday
  have : Numeric !{f '' s | f '' t} := by
    rw [numeric_def]
    simp_rw [moves_ofSets]
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      obtain ⟨a, hx', _⟩ := hf x
      obtain ⟨b, hy', _⟩ := hf y
      rw [← mk_lt_mk, hx', hy']
      exact H x hx y hy
    rintro (_ | _) _ ⟨y, hy, rfl⟩
    all_goals
      obtain ⟨hy, _, _⟩ := hf y
      exact hy
  have : !{s | t} = mk !{f '' s | f '' t} := by
    rw [← toGame_inj, toGame_ofSets, toGame_mk, Game.mk_ofSets]
    simp_rw [image_image]
    congr! with a ha a ha
    all_goals
    · obtain ⟨_, ha', _⟩ := hf a
      rw [← toGame_mk, toGame_inj, ha']
  rw [this]
  apply (birthday_mk_le _).trans
  simp_rw [IGame.birthday_ofSets, image_comp]
  congr! <;> aesop

theorem birthday_add_le (x y : Surreal) : (x + y).birthday ≤ x.birthday + y.birthday := by
  obtain ⟨a, _, ha, ha'⟩ := birthday_eq_iGameBirthday x
  obtain ⟨b, _, hb, hb'⟩ := birthday_eq_iGameBirthday y
  rw [← ha', ← hb', ← ha, ← hb, ← IGame.birthday_add]
  exact birthday_mk_le _

theorem birthday_sub_le (x y : Surreal) : (x - y).birthday ≤ x.birthday + y.birthday := by
  simpa using birthday_add_le x (-y)

/- This is currently an open problem, see https://mathoverflow.net/a/476829/147705. -/
proof_wanted birthday_mul_le (x y : Surreal) : (x * y).birthday ≤ x.birthday * y.birthday

/-- The birthday of a surreal number is at least the birthday of the corresponding game. -/
theorem birthday_toGame_le (x : Surreal) : x.toGame.birthday ≤ x.birthday := by
  obtain ⟨c, _, rfl, h⟩ := birthday_eq_iGameBirthday x
  rw [← h, toGame_mk]
  exact Game.birthday_mk_le c

/-! ### Small instances -/

/-- Surreals with a bounded birthday form a small set. -/
instance small_setOf_birthday_le (o : NatOrdinal.{u}) : Small.{u} {x | birthday x ≤ o} := by
  have h₁ : {x | birthday x ≤ o} ⊆ toGame ⁻¹' {x | x.birthday ≤ o} := by
    intro x hx
    exact x.birthday_toGame_le.trans hx
  have h₂ := Set.restrictPreimage_injective {x | x.birthday ≤ o} toGame.injective
  have : Small.{u} (toGame ⁻¹' {x | x.birthday ≤ o}) := small_of_injective h₂
  exact small_subset h₁

/-- Surreals with a bounded birthday form a small set. -/
instance small_setOf_birthday_lt (o : NatOrdinal.{u}) : Small.{u} {x | birthday x < o} := by
  refine small_subset (?_ : {x : Surreal | x.birthday < o} ⊆ {x : Surreal | x.birthday ≤ o})
  simp +contextual [le_of_lt]

/-- A variant of `small_setOf_birthday_le` in simp-normal form -/
instance small_subtype_birthday_le (o : NatOrdinal.{u}) : Small.{u} {x // birthday x ≤ o} :=
  small_setOf_birthday_le o

/-- A variant of `small_setOf_birthday_lt` in simp-normal form -/
instance small_subtype_birthday_lt (o : NatOrdinal.{u}) : Small.{u} {x // birthday x < o} :=
  small_setOf_birthday_lt o

/-! ### Surreals from intervals -/

theorem exists_birthday_lt_between {x y : Surreal} (h : x < y) (h' : x.birthday = y.birthday) :
    ∃ z ∈ Ioo x y, z.birthday < x.birthday := by
  obtain ⟨x, _, rfl, hx⟩ := birthday_eq_iGameBirthday x
  obtain ⟨y, _, rfl, hy⟩ := birthday_eq_iGameBirthday y
  rw [mk_lt_mk] at h
  have H : Numeric !{xᴸ | yᴿ} := by
    apply Numeric.mk <;> simp_rw [moves_ofSets]
    · exact fun a ha b hb ↦ (Numeric.left_lt ha).trans (h.trans (Numeric.lt_right hb))
    · rintro (_ | _) a ha <;> exact Numeric.of_mem_moves ha
  have Hle : !{xᴸ | yᴿ}.birthday < x.birthday := by
    apply lt_of_le_of_ne
    · rw [birthday_le_iff]
      rintro (_ | _) <;> simp_rw [moves_ofSets] <;> intro a ha
      · exact birthday_lt_of_mem_moves ha
      · rw [hx, h', ← hy]
        exact birthday_lt_of_mem_moves ha
    · intro hb
      apply h.not_antisymmRel
      trans !{xᴸ | yᴿ}
      · apply Fits.equiv_of_forall_birthday_le
        · constructor <;> simp_rw [moves_ofSets]
          · exact fun a ha ↦ (Numeric.left_lt ha).not_ge
          · exact fun a ha ↦ (h.trans <| Numeric.lt_right ha).not_ge
        · intro z _ hz
          apply le_birthday_of_fits


  refine ⟨@mk _ H, ?_, ?_⟩
  · constructor
    · apply lt_of_le_of_ne _ sorry
      generalize_proofs
      rw [mk_le_mk, le_iff_forall_lf]
      constructor
      · intro a ha
        apply not_le_of_gt
        apply Numeric.left_lt
        simpa
      · intro a ha
        apply not_le_of_gt
        apply h.trans
        apply Numeric.lt_right
        simpa using ha



#exit

/-- Returns the surreal with the least birthday in a given set.

This is intended to be used for `OrdConnected` nonempty sets, in which case the specified surreal is
unique. -/
def ofInterval (s : Set Surreal) : Surreal :=
  if h : s.Nonempty
    then Classical.choose (exists_minimalFor_of_wellFoundedLT (· ∈ s) birthday h)
    else 0

@[simp]
theorem ofInterval_empty : ofInterval ∅

theorem birthday_ofInterval_le {x : Surreal} {s : Set Surreal} (h : x ∈ s) :
    x.birthday ≤ (ofInterval s).birthday := by

end Surreal
