/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.Game.Ordinal
import CombinatorialGames.Game.Special
import Mathlib.Algebra.Order.Group.OrderIso
import Mathlib.Data.Fintype.Order

/-!
# Birthdays of games

There are two related but distinct notions of a birthday within combinatorial game theory. One is
the birthday of an `IGame`, which represents the "step" at which it is constructed. We define it
recursively as the least ordinal larger than the birthdays of its left and right options. On the
other hand, the birthday of a `Game` is the smallest birthday among all `IGame`s that quotient to
it.

The birthday of an `IGame` can be understood as representing the depth of its game tree. Meanwhile,
the birthday of a `Game` more closely matches Conway's original description. The lemma
`Game.birthday_eq_iGameBirthday` links both definitions together.
-/

universe u

open NatOrdinal Order Set
open scoped NaturalOps IGame

/-! ### Stuff for Mathlib -/

theorem IncompRel.ne {α : Type*} {r : α → α → Prop} [IsRefl α r] {a b : α}
    (h : IncompRel r a b) : a ≠ b := by
  rintro rfl
  exact h.1 <| refl_of r a

theorem ciSup_eq_bot {α : Type*} {ι : Sort*} [ConditionallyCompleteLinearOrderBot α] {f : ι → α}
    (hf : BddAbove (range f)) : ⨆ i, f i = ⊥ ↔ ∀ i, f i = ⊥ := by
  simpa using ciSup_le_iff' hf (a := ⊥)

@[simp]
theorem Set.empty_ne_singleton {α : Type*} (a : α) : ∅ ≠ ({a} : Set α) :=
  (Set.singleton_ne_empty a).symm

-- fix this! embarassing
@[simp]
theorem NatOrdinal.bot_eq_zero' : (⊥ : NatOrdinal) = 0 :=
  rfl

@[simp]
theorem NatOrdinal.succ_ne_zero (x : NatOrdinal) : succ x ≠ 0 :=
  Ordinal.succ_ne_zero x

@[simp]
protected theorem NatOrdinal.le_zero {x : NatOrdinal} : x ≤ 0 ↔ x = 0 :=
  Ordinal.le_zero

@[simp]
protected theorem NatOrdinal.succ_zero : succ (0 : NatOrdinal) = 1 :=
  Ordinal.succ_zero

@[simp]
protected theorem NatOrdinal.succ_one : succ (1 : NatOrdinal) = 2 := by
  rw [succ_eq_add_one, one_add_one_eq_two]

protected theorem NatOrdinal.lt_iSup_iff {ι : Type*} [Small.{u} ι] (f : ι → NatOrdinal.{u}) {x} :
    x < ⨆ i, f i ↔ ∃ i, x < f i :=
  Ordinal.lt_iSup_iff

protected theorem NatOrdinal.iSup_eq_zero_iff {ι : Type*} [Small.{u} ι] {f : ι → NatOrdinal.{u}} :
    ⨆ i, f i = 0 ↔ ∀ i, f i = 0 :=
  Ordinal.iSup_eq_zero_iff

theorem NatOrdinal.lt_omega0 {o : NatOrdinal} :
    o < of Ordinal.omega0 ↔ ∃ n : ℕ, o = n := by
  rw [← of_val o, OrderIso.lt_iff_lt, Ordinal.lt_omega0]
  simp [← val_natCast]

theorem NatOrdinal.nat_lt_omega0 (n : ℕ) : n < of Ordinal.omega0 := by
  rw [NatOrdinal.lt_omega0]
  use n

/-! ### `IGame` birthday -/

namespace IGame

/-- The birthday of an `IGame` is inductively defined as the least strict upper bound of the
birthdays of its options. It may be thought as the "step" in which a certain game is constructed. -/
noncomputable def birthday (x : IGame.{u}) : NatOrdinal.{u} :=
  ⨆ y : {y // IsOption y x}, succ (birthday y)
termination_by x
decreasing_by igame_wf

theorem lt_birthday_iff' {x : IGame} {o : NatOrdinal} : o < x.birthday ↔
    ∃ y, IsOption y x ∧ o ≤ y.birthday := by
  rw [birthday, NatOrdinal.lt_iSup_iff]
  simp

theorem birthday_le_iff' {x : IGame} {o : NatOrdinal} : x.birthday ≤ o ↔
    ∀ y, IsOption y x → y.birthday < o := by
  simpa using lt_birthday_iff'.not

theorem lt_birthday_iff {x : IGame} {o : NatOrdinal} : o < x.birthday ↔
    (∃ y ∈ x.leftMoves, o ≤ y.birthday) ∨ (∃ y ∈ x.rightMoves, o ≤ y.birthday) := by
  simp [lt_birthday_iff', IsOption, or_and_right, exists_or]

theorem birthday_le_iff {x : IGame} {o : NatOrdinal} : x.birthday ≤ o ↔
    (∀ y ∈ x.leftMoves, y.birthday < o) ∧ (∀ y ∈ x.rightMoves, y.birthday < o) := by
  simpa using lt_birthday_iff.not

theorem birthday_eq_max (x : IGame) : birthday x =
    max (⨆ y : x.leftMoves, succ y.1.birthday) (⨆ y : x.rightMoves, succ y.1.birthday) := by
  apply eq_of_forall_lt_iff
  simp [lt_birthday_iff, NatOrdinal.lt_iSup_iff]

@[aesop apply unsafe 50%]
theorem birthday_lt_of_mem_leftMoves {x y : IGame} (hy : y ∈ x.leftMoves) :
    y.birthday < x.birthday :=
  lt_birthday_iff.2 (.inl ⟨y, hy, le_rfl⟩)

@[aesop apply unsafe 50%]
theorem birthday_lt_of_mem_rightMoves {x y : IGame} (hy : y ∈ x.rightMoves) :
    y.birthday < x.birthday :=
  lt_birthday_iff.2 (.inr ⟨y, hy, le_rfl⟩)

theorem birthday_lt_of_isOption {x y : IGame} (hy : IsOption y x) : y.birthday < x.birthday :=
  lt_birthday_iff'.2 ⟨y, hy, le_rfl⟩

theorem birthday_lt_of_subposition {x y : IGame} (hy : Subposition y x) :
    y.birthday < x.birthday := by
  cases hy with
  | single h => exact birthday_lt_of_isOption h
  | tail IH h => exact (birthday_lt_of_subposition IH).trans (birthday_lt_of_isOption h)
termination_by x
decreasing_by igame_wf

theorem birthday_ofSets (s t : Set IGame.{u}) [Small.{u} s] [Small.{u} t] :
    birthday {s | t}ᴵ = max (sSup (succ ∘ birthday '' s)) (sSup (succ ∘ birthday '' t)) := by
  rw [birthday_eq_max, leftMoves_ofSets, rightMoves_ofSets]
  simp [iSup, image_eq_range]

@[simp]
theorem birthday_eq_zero {x : IGame} : birthday x = 0 ↔ x = 0 := by
  rw [birthday, NatOrdinal.iSup_eq_zero_iff, IGame.ext_iff]
  simp [IsOption, forall_and, eq_empty_iff_forall_notMem]

@[simp] theorem birthday_zero : birthday 0 = 0 := by simp
@[simp] theorem birthday_one : birthday 1 = 1 := by rw [one_def, birthday_ofSets]; simp
@[simp] theorem birthday_star : birthday ⋆ = 1 := by rw [star, birthday_ofSets]; simp

@[simp]
theorem birthday_half : birthday ½ = 2 := by
  rw [half, birthday_ofSets]
  simp

@[simp]
theorem birthday_up : birthday ↑ = 2 := by
  rw [up, birthday_ofSets]
  simp

@[simp]
theorem birthday_down : birthday ↓ = 2 := by
  rw [down, birthday_ofSets]
  simp

@[simp]
theorem birthday_neg (x : IGame) : (-x).birthday = x.birthday := by
  refine eq_of_forall_lt_iff fun y ↦ ?_
  rw [lt_birthday_iff, lt_birthday_iff, exists_leftMoves_neg, exists_rightMoves_neg, or_comm]
  congr! 3
  all_goals
    rw [← and_congr_right]
    intro h
    rw [birthday_neg]
termination_by x
decreasing_by igame_wf

@[simp]
theorem birthday_toIGame (o : NatOrdinal) : o.toIGame.birthday = o := by
  rw [toIGame_def, birthday_ofSets, image_empty, csSup_empty, max_bot_right, image_image]
  conv_rhs => rw [← iSup_succ o, iSup]
  simp_rw [Function.comp_apply, ← image_eq_range]
  congr!
  rw [birthday_toIGame]
termination_by o

theorem le_toIGame_birthday (x : IGame) : x ≤ x.birthday.toIGame := by
  rw [le_iff_forall_lf]
  refine ⟨fun y hy ↦ ((le_toIGame_birthday y).trans_lt ?_).not_ge, ?_⟩
  · simpa using birthday_lt_of_mem_leftMoves hy
  · simp
termination_by x
decreasing_by igame_wf

theorem neg_toIGame_birthday_le (x : IGame) : -x.birthday.toIGame ≤ x := by
  simpa [IGame.neg_le] using le_toIGame_birthday (-x)

@[simp]
theorem birthday_add (x y : IGame) : (x + y).birthday = x.birthday + y.birthday := by
  refine eq_of_forall_lt_iff fun o ↦ ?_
  simp_rw [lt_add_iff, lt_birthday_iff, exists_leftMoves_add, exists_rightMoves_add, or_and_right,
    exists_or, or_or_or_comm]
  congr! 2
  all_goals
    constructor
    · rintro ⟨z, hz, hz'⟩
      refine ⟨_, ⟨z, hz, le_rfl⟩, ?_⟩
      rwa [← birthday_add]
    · rintro ⟨a, ⟨⟨z, hz, hz'⟩, ha⟩⟩
      use z, hz
      rw [birthday_add]
      apply ha.trans
      first | exact add_le_add_left hz' _ | exact add_le_add_right hz' _
termination_by (x, y)
decreasing_by igame_wf

@[simp]
theorem birthday_sub (x y : IGame) : (x - y).birthday = x.birthday + y.birthday := by
  simp [sub_eq_add_neg]

@[simp, norm_cast]
theorem birthday_natCast : ∀ n : ℕ, birthday n = n
  | 0 => birthday_zero
  | n + 1 => by simp_rw [Nat.cast_add_one, birthday_add, birthday_natCast, birthday_one]

@[simp]
theorem birthday_ofNat (n : ℕ) [n.AtLeastTwo] : birthday ofNat(n) = n :=
  birthday_natCast n

@[simp]
theorem birthday_tiny (x : IGame) : (⧾x).birthday = x.birthday + 2 := by
  simp [tiny, Order.succ_eq_add_one, birthday_ofSets, ← one_add_one_eq_two, ← add_assoc]

@[simp]
theorem birthday_miny (x : IGame) : (⧿x).birthday = x.birthday + 2 := by
  rw [← neg_tiny, birthday_neg, birthday_tiny]

/-- Games with a bounded birthday form a small set. -/
instance small_setOf_birthday_lt (o : NatOrdinal.{u}) : Small.{u} {x | birthday x < o} := by
  induction o using SuccOrder.prelimitRecOn with
  | succ o _ ih =>
    apply small_subset
      (s := range fun s : Set {x | birthday x < o} × Set {x | birthday x < o} ↦ {s.1 | s.2}ᴵ)
    refine fun x hx ↦ ⟨((↑) ⁻¹' x.leftMoves, (↑) ⁻¹' x.rightMoves), ?_⟩
    simp_rw [lt_succ_iff, birthday_le_iff] at hx
    ext <;> simp_all
  | isSuccPrelimit o ho ih =>
    convert @small_biUnion _ _ (Iio o) _ (fun i _ => {x : IGame.{u} | x.birthday < i}) ih
    ext x
    simpa using ho.lt_iff_exists_lt

/-- Games with a bounded birthday form a small set. -/
instance small_setOf_birthday_le (o : NatOrdinal.{u}) : Small.{u} {x | birthday x ≤ o} := by
  convert small_setOf_birthday_lt (succ o) using 1
  simp

/-- A variant of `small_setOf_birthday_le` in simp-normal form -/
instance small_subtype_birthday_le (o : NatOrdinal.{u}) : Small.{u} {x // birthday x ≤ o} :=
  small_setOf_birthday_le o

/-- A variant of `small_setOf_birthday_lt` in simp-normal form -/
instance small_subtype_birthday_lt (o : NatOrdinal.{u}) : Small.{u} {x // birthday x < o} :=
  small_setOf_birthday_lt o

/-! #### Short games -/

/-- The finset of all games with birthday ≤ n. -/
noncomputable def birthdayFinset : ℕ → Finset IGame.{u}
  | 0 => {0}
  | n + 1 => ((birthdayFinset n).powerset ×ˢ (birthdayFinset n).powerset).map
    ⟨fun ⟨a, b⟩ => {a | b}ᴵ, fun a b hab => by aesop⟩

theorem mem_birthdayFinset_succ {x : IGame} {n : ℕ} : x ∈ birthdayFinset (n + 1) ↔
    ∃ l r, (l ⊆ birthdayFinset n ∧ r ⊆ birthdayFinset n) ∧ {l | r}ᴵ = x := by
  simp [birthdayFinset]

@[simp] theorem birthdayFinset_zero : birthdayFinset 0 = {0} := rfl

theorem birthdayFinset_one :
    birthdayFinset 1 = ⟨[0, 1, -1, ⋆], by aesop (add simp [IGame.ext_iff])⟩ := by
  ext
  rw [mem_birthdayFinset_succ]
  aesop (add simp [IGame.ext_iff])

@[simp]
theorem card_birthdayFinset (n : ℕ) :
    (birthdayFinset.{u} (n + 1)).card = 4 ^ (birthdayFinset.{u} n).card := by
  rw [birthdayFinset, Finset.card_map, Finset.card_product, Finset.card_powerset, ← mul_pow]
  rfl

theorem mem_birthdayFinset_of_isOption {x y : IGame} {n : ℕ} (hnx : x ∈ birthdayFinset (n + 1))
    (hy : IsOption y x) : y ∈ birthdayFinset n := by
  rw [mem_birthdayFinset_succ] at hnx
  aesop

@[simp]
theorem mem_birthdayFinset {x : IGame} {n : ℕ} : x ∈ birthdayFinset n ↔ x.birthday ≤ n := by
  induction n generalizing x with
  | zero => simp
  | succ n IH =>
    simp_rw [mem_birthdayFinset_succ, birthday_le_iff, Finset.subset_iff, Nat.cast_add_one,
      ← succ_eq_add_one, lt_succ_iff, IH]
    constructor
    · aesop
    · rintro ⟨hl, hr⟩
      have hxl : x.leftMoves ⊆ birthdayFinset n := by intro y; simp_all
      have hxr : x.rightMoves ⊆ birthdayFinset n := by intro y; simp_all
      classical
      have := Set.fintypeSubset _ hxl
      have := Set.fintypeSubset _ hxr
      use x.leftMoves.toFinset, x.rightMoves.toFinset
      aesop

theorem strictMono_birthdayFinset : StrictMono birthdayFinset := by
  refine strictMono_nat_of_lt_succ fun n ↦ ⟨fun y hy ↦ ?_, fun h ↦ ?_⟩
  · rw [mem_birthdayFinset] at *
    apply hy.trans
    simp
  · have := Finset.card_le_card h
    rw [card_birthdayFinset] at this
    exact (Nat.lt_pow_self (Nat.one_lt_succ_succ 2)).not_ge this

theorem short_iff_birthday_finite {x : IGame} :
    x.Short ↔ x.birthday < of Ordinal.omega0 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have (y : {y // IsOption y x}) : ∃ n : ℕ, birthday y = n := by
      rw [← NatOrdinal.lt_omega0, ← short_iff_birthday_finite]
      exact h.isOption y.2
    choose f hf using this
    obtain ⟨n, hn⟩ := (finite_range f).exists_le
    apply lt_of_le_of_lt _ (NatOrdinal.nat_lt_omega0 (n + 1))
    rw [birthday_le_iff', Nat.cast_add_one, ← succ_eq_add_one]
    aesop
  · rw [NatOrdinal.lt_omega0, short_iff_finite_setOf_subposition]
    intro ⟨n, hn⟩
    apply (birthdayFinset n).finite_toSet.subset fun y hy ↦ ?_
    simpa using (birthday_lt_of_subposition hy).le.trans_eq hn
termination_by x
decreasing_by igame_wf

theorem Short.birthday_lt_omega0 (x : IGame) [Short x] : birthday x < of Ordinal.omega0 :=
  short_iff_birthday_finite.1 ‹_›

end IGame

/-! ### `Game` birthday -/

namespace Game

/-- The birthday of a game is defined as the least birthday among all pre-games that define it. -/
noncomputable def birthday (x : Game.{u}) : NatOrdinal.{u} :=
  sInf (IGame.birthday '' (mk ⁻¹' {x}))

theorem birthday_eq_iGameBirthday (x : Game) :
    ∃ y : IGame, Game.mk y = x ∧ y.birthday = birthday x := by
  refine csInf_mem (image_nonempty.2 ?_)
  exact ⟨_, x.out_eq⟩

theorem birthday_mk_le (x : IGame) : birthday (mk x) ≤ x.birthday :=
  csInf_le' ⟨x, rfl, rfl⟩

@[simp]
theorem birthday_zero : birthday 0 = 0 := by
  simpa using birthday_mk_le 0

@[simp]
theorem birthday_eq_zero {x : Game} : birthday x = 0 ↔ x = 0 := by
  obtain ⟨_, _, _⟩ := birthday_eq_iGameBirthday x
  refine ⟨fun _ ↦ ?_, ?_⟩ <;> simp_all

private theorem birthday_neg_le (x : Game) : (-x).birthday ≤ x.birthday := by
  obtain ⟨y, hy, hy'⟩ := birthday_eq_iGameBirthday x
  rw [← hy', ← hy]
  apply (birthday_mk_le _).trans
  rw [IGame.birthday_neg]

@[simp]
theorem birthday_neg (x : Game) : (-x).birthday = x.birthday := by
  apply (birthday_neg_le x).antisymm
  simpa using birthday_neg_le (-x)

theorem le_toGame_birthday (x : Game) : x ≤ x.birthday.toGame := by
  obtain ⟨y, hy, hy'⟩ := birthday_eq_iGameBirthday x
  rw [← hy', ← hy]
  exact y.le_toIGame_birthday

theorem neg_toGame_birthday_le (x : Game) : -x.birthday.toGame ≤ x := by
  simpa [neg_le] using le_toGame_birthday (-x)

@[simp]
theorem birthday_toGame (o : NatOrdinal) : birthday o.toGame = o := by
  apply le_antisymm
  · simpa using birthday_mk_le o.toIGame
  · simpa using o.toGame.le_toGame_birthday

@[simp, norm_cast]
theorem birthday_natCast (n : ℕ) : birthday n = n := by
  simpa using birthday_toGame n

@[simp]
theorem birthday_ofNat (n : ℕ) [n.AtLeastTwo] : birthday ofNat(n) = n :=
  birthday_natCast n

@[simp]
theorem birthday_one : birthday 1 = 1 := by
  simpa using birthday_natCast 1

@[simp]
theorem birthday_star : birthday (Game.mk ⋆) = 1 := by
  apply le_antisymm
  · simpa using birthday_mk_le ⋆
  · rw [Ordinal.one_le_iff_ne_zero, birthday_eq_zero.ne]
    exact IncompRel.ne (r := (· ≤ ·)) (IGame.star_fuzzy_zero)

theorem birthday_ofSets_le {s t : Set Game.{u}} [Small.{u} s] [Small.{u} t] :
    birthday {s | t}ᴳ ≤ max (sSup (succ ∘ birthday '' s)) (sSup (succ ∘ birthday '' t)) := by
  choose f hf using birthday_eq_iGameBirthday
  trans {f '' s | f '' t}ᴵ.birthday
  · convert birthday_mk_le {f '' s | f '' t}ᴵ using 2
    simp_rw [mk_ofSets, image_image]
    aesop
  · simp_rw [IGame.birthday_ofSets, image_comp]
    congr! <;> aesop

theorem birthday_add_le (x y : Game) : (x + y).birthday ≤ x.birthday + y.birthday := by
  obtain ⟨a, ha, ha'⟩ := birthday_eq_iGameBirthday x
  obtain ⟨b, hb, hb'⟩ := birthday_eq_iGameBirthday y
  rw [← ha', ← hb', ← ha, ← hb, ← IGame.birthday_add]
  exact birthday_mk_le _

theorem birthday_sub_le (x y : Game) : (x - y).birthday ≤ x.birthday + y.birthday := by
  simpa using birthday_add_le x (-y)

/-- Games with a bounded birthday form a small set. -/
instance small_setOf_birthday_le (o : NatOrdinal.{u}) : Small.{u} {x | birthday x ≤ o} := by
  refine small_subset (s := mk '' {x | IGame.birthday x ≤ o}) fun x hx ↦ ?_
  obtain ⟨y, rfl, hy⟩ := birthday_eq_iGameBirthday x
  exact mem_image_of_mem mk (hy.trans_le hx)

/-- Games with a bounded birthday form a small set. -/
instance small_setOf_birthday_lt (o : NatOrdinal.{u}) : Small.{u} {x | birthday x < o} :=
  small_subset (s := {x | birthday x ≤ o}) <| setOf_subset_setOf.2 fun _ => le_of_lt

/-- A variant of `small_setOf_birthday_le` in simp-normal form -/
instance small_subtype_birthday_le (o : NatOrdinal.{u}) : Small.{u} {x // birthday x ≤ o} :=
  small_setOf_birthday_le o

/-- A variant of `small_setOf_birthday_lt` in simp-normal form -/
instance small_subtype_birthday_lt (o : NatOrdinal.{u}) : Small.{u} {x // birthday x < o} :=
  small_setOf_birthday_lt o

end Game
