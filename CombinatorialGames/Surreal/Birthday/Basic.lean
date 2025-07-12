/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
import CombinatorialGames.Game.Birthday
import CombinatorialGames.Surreal.Ordinal

universe u
noncomputable section

namespace Surreal
open IGame NatOrdinal Order Set

/--
The birthday of a surreal number is defined as the least birthday
among all *numeric* pre-games that define it. -/
def birthday (x : Surreal.{u}) : NatOrdinal.{u} :=
  sInf (IGame.birthday '' {c | ∃ _ : Numeric c, mk c = x})

theorem birthday_eq_iGameBirthday (x : Surreal) :
    ∃ (y : IGame) (_ : Numeric y), mk y = x ∧ y.birthday = birthday x := by
  have h : (IGame.birthday '' {c | ∃ _ : Numeric c, mk c = x}).Nonempty := by
    rw [image_nonempty]
    exact ⟨_, _, x.out_eq⟩
  obtain ⟨c, ⟨cn, rfl⟩, hc⟩ := csInf_mem h
  exact ⟨c, cn, rfl, hc⟩

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
  obtain ⟨y, _, hy, hy'⟩ := birthday_eq_iGameBirthday x
  rw [← hy', ← hy]
  apply (birthday_mk_le _).trans
  rw [IGame.birthday_neg]

@[simp]
theorem birthday_neg (x : Surreal) : (-x).birthday = x.birthday := by
  apply (birthday_neg_le x).antisymm
  simpa using birthday_neg_le (-x)

theorem le_toSurreal_birthday (x : Surreal) : x ≤ x.birthday.toSurreal := by
  obtain ⟨y, _, hy, hy'⟩ := birthday_eq_iGameBirthday x
  rw [← hy', ← hy]
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

theorem birthday_add_le (x y : Surreal) : (x + y).birthday ≤ x.birthday + y.birthday := by
  obtain ⟨a, _, ha, ha'⟩ := birthday_eq_iGameBirthday x
  obtain ⟨b, _, hb, hb'⟩ := birthday_eq_iGameBirthday y
  rw [← ha', ← hb', ← ha, ← hb, ← IGame.birthday_add]
  exact birthday_mk_le _

theorem birthday_sub_le (x y : Surreal) : (x - y).birthday ≤ x.birthday + y.birthday := by
  simpa using birthday_add_le x (-y)

/- The bound `(x * y).birthday ≤ x.birthday * y.birthday` on surreals is currently an open problem.
See https://mathoverflow.net/a/476829/147705. -/

/--
The birthday of a surreal number is at least the birthday of the corresponding game.
For the equality, see `CombinatorialGames.Surreal.Birthday.Equal`.
-/
theorem birthday_toGame_le (x : Surreal) : x.toGame.birthday ≤ x.birthday := by
  obtain ⟨c, _, rfl, h⟩ := birthday_eq_iGameBirthday x
  rw [← h, toGame_mk]
  exact Game.birthday_mk_le c

/-- Surreals with a bounded birthday form a small set. -/
instance small_setOf_birthday_le (o : NatOrdinal.{u}) : Small.{u} {x | birthday x ≤ o} := by
  have h₁ : {x | birthday x ≤ o} ⊆ toGame ⁻¹' {x | x.birthday ≤ o} := by
    intro x hx
    exact x.birthday_toGame_le.trans hx
  have h₂ := Set.restrictPreimage_injective {x | x.birthday ≤ o} toGame.injective
  have : Small.{u} (toGame ⁻¹' {x | x.birthday ≤ o}):= small_of_injective h₂
  exact small_subset h₁

/-- Surreals with a bounded birthday form a small set. -/
instance small_setOf_birthday_lt (o : NatOrdinal.{u}) : Small.{u} {x | birthday x < o} := by
  apply @small_subset _ _ _ _ (small_setOf_birthday_le o)
  exact fun x (hx : x.birthday < _) ↦ le_of_lt hx

theorem birthday_ofSets_le {s t : Set Surreal.{u}} [Small.{u} s] [Small.{u} t]
    (H : ∀ l ∈ s, ∀ r ∈ t, l < r) :
    birthday (ofSets s t H) ≤ max (⨆ l ∈ s, succ (birthday l)) (⨆ r ∈ t, succ (birthday r)) := by
  let u (s : Surreal) := (birthday_eq_iGameBirthday s).choose
  have nu (s : Surreal) : Numeric (u s) := (birthday_eq_iGameBirthday s).choose_spec.1
  have nk (s : Surreal) : mk (u s) = s := (birthday_eq_iGameBirthday s).choose_spec.2.1
  have nc (s : Surreal) : (u s).birthday = s.birthday :=
    (birthday_eq_iGameBirthday s).choose_spec.2.2
  have nn : Numeric {u '' s | u '' t}ᴵ := by
    rw [numeric_def]
    simp +contextual [nu, ← Surreal.mk_lt_mk, nk, H]
  have h : mk {u '' s | u '' t}ᴵ = {s | t}ˢ := by
    rw [mk_ofSets]
    congr
    · ext x
      constructor
      · rintro ⟨⟨_, ⟨x, hx, rfl⟩⟩, rfl⟩
        simp [nk, hx]
      · intro hx
        exact ⟨⟨u x, mem_image_of_mem u hx⟩, nk x⟩
    · ext x
      constructor
      · rintro ⟨⟨_, ⟨x, hx, rfl⟩⟩, rfl⟩
        simp [nk, hx]
      · intro hx
        exact ⟨⟨u x, mem_image_of_mem u hx⟩, nk x⟩
  rw [← h]
  apply (birthday_mk_le _).trans
  rw [birthday_le_iff]
  simp only [leftMoves_ofSets, mem_image, lt_sup_iff, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, rightMoves_ofSets]
  constructor
  · intro z hz
    left
    rw [← Ordinal.NatOrdinal.iSup_subtype, NatOrdinal.lt_iSup_iff]
    exact ⟨⟨z, hz⟩, by simp [nc]⟩
  · intro z hz
    right
    rw [← Ordinal.NatOrdinal.iSup_subtype, NatOrdinal.lt_iSup_iff]
    exact ⟨⟨z, hz⟩, by simp [nc]⟩

end Surreal
