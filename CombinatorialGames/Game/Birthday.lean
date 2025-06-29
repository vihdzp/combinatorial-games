/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import CombinatorialGames.Game.Ordinal
import CombinatorialGames.Game.Special
import Mathlib.Algebra.Order.Group.OrderIso

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
  simp [IsOption, forall_and, eq_empty_iff_forall_not_mem]

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
  refine ⟨fun y hy ↦ ((le_toIGame_birthday y).trans_lt ?_).not_le, ?_⟩
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
instance small_setOf_birthday_le (o : NatOrdinal.{u}) : Small.{u} {x // birthday x ≤ o} := by
  have (y : Iio o) := have := y.2; small_setOf_birthday_le y.1
  have : Small.{u} {x // birthday x < o} := by
    convert @small_iUnion _ _ _ _ fun y : Iio o ↦ have := y.2; small_setOf_birthday_le y.1
    change _ ↔ _ ∈ ⋃ y : Iio o, {x : IGame | x.birthday ≤ y.1}
    simpa using ⟨fun hy ↦ ⟨_, hy, le_rfl⟩, fun ⟨a, ha, ha'⟩ ↦  ha'.trans_lt ha⟩
  let f (y : Set {x // birthday x < o} × Set {x // birthday x < o}) : {x // birthday x ≤ o} := by
    refine ⟨{Subtype.val '' y.1 | Subtype.val '' y.2}ᴵ, ?_⟩
    rw [birthday_ofSets, max_le_iff,
      csSup_le_iff' (Ordinal.bddAbove_of_small _), csSup_le_iff' (Ordinal.bddAbove_of_small _)]
    aesop
  have hl (x : {x // birthday x ≤ o}) (y : x.1.leftMoves) : birthday y.1 < o :=
    (birthday_lt_of_mem_leftMoves y.2).trans_le x.2
  have hr (x : {x // birthday x ≤ o}) (y : x.1.rightMoves) : birthday y.1 < o :=
    (birthday_lt_of_mem_rightMoves y.2).trans_le x.2
  refine small_of_surjective (f := f) fun x ↦
    ⟨⟨range fun y : x.1.leftMoves ↦ ⟨y, hl x y⟩, range fun y : x.1.rightMoves ↦ ⟨y, hr x y⟩⟩, ?_⟩
  aesop
termination_by o

/-- Games with a bounded birthday form a small set. -/
instance small_setOf_birthday_lt (o : NatOrdinal.{u}) : Small.{u} {x // birthday x < o} := by
  apply @small_subset _ _ _ _ (small_setOf_birthday_le o)
  exact fun x (hx : x.birthday < _) ↦ le_of_lt hx

/-- The finset of all games with birthday ≤ n. -/
noncomputable def birthdayFinset : ℕ → Finset IGame.{u}
  | 0 => {0}
  | n + 1 => ((birthdayFinset n).powerset ×ˢ (birthdayFinset n).powerset).map
    ⟨fun ⟨a, b⟩ => {a | b}ᴵ, fun a b hab => by aesop⟩

theorem birthdayFinset_mem_succ_iff {x : IGame} {n : ℕ} :
  x ∈ birthdayFinset (n + 1) ↔
    ∃ l r, (l ⊆ birthdayFinset n ∧ r ⊆ birthdayFinset n) ∧ {↑l | ↑r}ᴵ = x := by
  simp [birthdayFinset]

@[simp] theorem birthdayFinset_zero : birthdayFinset 0 = {0} := rfl

@[simp] theorem card_birthdayFinset_one : (birthdayFinset 1).card = 4 := by simp [birthdayFinset]

@[simp]
theorem card_birthdayFinset (n : ℕ) :
    (birthdayFinset.{u} (n + 1)).card = 4 ^ (birthdayFinset.{u} n).card := by
  rw [birthdayFinset, Finset.card_map, Finset.card_product, Finset.card_powerset, ← mul_pow]
  simp only [Nat.reduceMul]

theorem birthday_finset_option {x y : IGame} {n : ℕ} (hnx : x ∈ birthdayFinset (n + 1))
    (hy : IsOption y x) : y ∈ birthdayFinset n := by
  rw [birthdayFinset_mem_succ_iff] at hnx
  obtain ⟨xl, xr, ⟨⟨hxl, hxr⟩, rfl⟩⟩ := hnx
  cases hy with
  | inl hy =>
    rw [leftMoves_ofSets, Finset.mem_coe] at hy
    exact hxl hy
  | inr hy =>
    rw [rightMoves_ofSets, Finset.mem_coe] at hy
    exact hxr hy

theorem mem_birthdayFinset_of_birthday_le {x : IGame.{u}} {n : ℕ} (hxn : x.birthday ≤ n) :
    x ∈ birthdayFinset n := by
  unfold birthdayFinset
  split
  · rw [Finset.mem_singleton]
    rwa [Nat.cast_zero, NatOrdinal.le_zero, birthday_eq_zero] at hxn
  · rename_i k
    rw [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] at hxn
    simp_rw [Finset.mem_map, Finset.mem_product, Finset.mem_powerset, Function.Embedding.coeFn_mk,
      Prod.exists]
    have hx : ∀ y, IsOption y x → y ∈ birthdayFinset k := fun y hy => by
      have hxn := (birthday_lt_of_mem_option hy).trans_le hxn
      rw [← Nat.cast_add_one, ← OrderIso.lt_iff_lt NatOrdinal.toOrdinal,
        toOrdinal_cast_nat, Nat.cast_add_one, Ordinal.lt_add_iff Ordinal.one_ne_zero] at hxn
      obtain ⟨o, ⟨ho, hxn⟩⟩ := hxn
      rw [Ordinal.lt_one_iff_zero] at ho
      rw [← OrderIso.le_iff_le Ordinal.toNatOrdinal, toOrdinal_toNatOrdinal, ho,
        add_zero, Ordinal.toNatOrdinal_cast_nat] at hxn
      exact mem_birthdayFinset_of_birthday_le hxn
    have hxl : x.leftMoves ⊆ birthdayFinset k := (hx · <| IsOption.of_mem_leftMoves ·)
    have hxr : x.rightMoves ⊆ birthdayFinset k := (hx · <| IsOption.of_mem_rightMoves ·)
    classical
    have := Set.fintypeSubset _ hxl
    have := Set.fintypeSubset _ hxr
    use x.leftMoves.toFinset, x.rightMoves.toFinset
    simp_rw [toFinset_subset, coe_toFinset, ofSets_leftMoves_rightMoves, and_true]
    exact union_subset_iff.mp hx

theorem birthday_le_of_mem_birthdayFinset {x : IGame} {n : ℕ} (hxn : x ∈ birthdayFinset n) :
    x.birthday ≤ n := by
  unfold birthdayFinset at hxn
  split at hxn
  · rw [Finset.mem_singleton] at hxn
    simp_rw [hxn, birthday_zero, Nat.cast_zero, le_refl]
  · rename_i k
    simp_rw [Finset.mem_map, Finset.mem_product, Finset.mem_powerset,
      Function.Embedding.coeFn_mk, Prod.exists] at hxn
    obtain ⟨l, r, ⟨⟨hl, hr⟩, hlr⟩⟩ := hxn
    rw [birthday_eq_max, sup_le_iff]
    refine ⟨ciSup_le' fun ⟨y, hy⟩ => ?_, ciSup_le' fun ⟨y, hy⟩ => ?_⟩
    all_goals rw [Nat.cast_add_one, succ_le_iff]
    · have : y.birthday ≤ k := by
        rw [← hlr, leftMoves_ofSets, Finset.mem_coe] at hy
        exact birthday_le_of_mem_birthdayFinset <| hl hy
      exact lt_add_one_iff.mpr this
    · have : y.birthday ≤ k := by
        rw [← hlr, rightMoves_ofSets, Finset.mem_coe] at hy
        exact birthday_le_of_mem_birthdayFinset <| hr hy
      exact lt_add_one_iff.mpr this

@[simp] theorem mem_birthdayFinset {x : IGame} {n : ℕ} :
    x ∈ birthdayFinset n ↔ x.birthday ≤ n :=
  ⟨birthday_le_of_mem_birthdayFinset, mem_birthdayFinset_of_birthday_le⟩

theorem birthday_finset_strictMono : StrictMono birthdayFinset := by
  apply strictMono_nat_of_lt_succ
  intro n
  constructor
  · intro x hx
    apply mem_birthdayFinset_of_birthday_le
    rw [mem_birthdayFinset] at hx
    apply hx.trans
    rw [Nat.cast_le]
    exact Nat.le_add_right n 1
  · rw [Finset.not_subset]
    induction n with
    | zero =>
      refine ⟨1, by simp, by simp⟩
    | succ n hn =>
      obtain ⟨g, hg⟩ := hn
      use g + 1
      constructor <;> simp_all

theorem leftMoves_finite_birthday_nat {x : IGame} (hx : x.birthday < Ordinal.omega0)
    : x.leftMoves.Finite := by
  rw [Ordinal.lt_omega0] at hx
  obtain ⟨n, hn⟩ := hx
  apply_fun Ordinal.toNatOrdinal at hn
  rw [Ordinal.toNatOrdinal_cast_nat] at hn
  apply le_of_eq at hn
  cases n with
  | zero =>
    rw [Nat.cast_zero, NatOrdinal.le_zero, Ordinal.toNatOrdinal_eq_zero, birthday_eq_zero] at hn
    rw [hn, leftMoves_zero]
    exact finite_empty
  | succ n =>
    obtain ⟨l, _, ⟨hl, _, h⟩⟩ := birthdayFinset_mem_succ_iff.mp <| mem_birthdayFinset_of_birthday_le hn
    rw [leftMoves_ofSets]
    exact Finset.finite_toSet l

theorem rightMoves_finite_birthday_nat {x : IGame}
    (hx : x.birthday < Ordinal.omega0)
    : x.rightMoves.Finite := by
  rw [← birthday_neg] at hx
  rw [show x.rightMoves = -(-x).leftMoves by simp,
    ← Set.image_neg_eq_neg]
  exact Set.Finite.image (fun x => -x) (leftMoves_finite_birthday_nat hx)

theorem short_iff_birthday_finite (x : IGame) : x.Short ↔ x.birthday < Ordinal.omega0 := by
  rw [short_def]
  refine ⟨fun ⟨hfl, hfr, hl, hr⟩ => ?_, fun h => ?_⟩
  · rw [birthday_eq_max, sup_lt_iff]
    -- TODO: these declarations have to be definition-casted.
    -- is there a nicer way we can work around explicit finiteness here?
    have : Finite x.leftMoves := hfl
    have : Finite x.rightMoves := hfr
    constructor
    on_goal 1 =>
      by_cases h : IsEmpty x.leftMoves
      · rw [ciSup_of_empty, NatOrdinal.bot_eq_zero']
        exact Ordinal.nat_lt_omega0 0
    on_goal 2 =>
      by_cases h : IsEmpty x.rightMoves
      · rw [ciSup_of_empty, NatOrdinal.bot_eq_zero']
        exact Ordinal.nat_lt_omega0 0
    all_goals
      have := Set.Nonempty.ciSup_lt_iff (a := Ordinal.omega0) (f := fun y => succ (y.val).birthday)
        (nonempty_iff_univ_nonempty.mp (not_isEmpty_iff.mp h)) (Set.finite_univ)
      simp_rw [mem_univ, ciSup_unique, forall_const, Subtype.forall] at this
      rw [this]
      intro y hy
      rw [Ordinal.lt_omega0]
    · obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp <| (short_iff_birthday_finite y).mp (hl y hy)
      use succ n
      rw [hn, ← Ordinal.natCast_succ, Nat.succ_eq_succ]
    · obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp <| (short_iff_birthday_finite y).mp (hr y hy)
      use succ n
      rw [hn, ← Ordinal.natCast_succ, Nat.succ_eq_succ]
  · refine ⟨?_, ?_, fun y hy => ?_, fun y hy => ?_⟩
    · exact leftMoves_finite_birthday_nat h
    · exact rightMoves_finite_birthday_nat h
    · exact (short_iff_birthday_finite y).mpr ((birthday_lt_of_mem_leftMoves hy).trans h)
    · exact (short_iff_birthday_finite y).mpr ((birthday_lt_of_mem_rightMoves hy).trans h)
termination_by x
decreasing_by igame_wf

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

theorem birthday_add_le (x y : Game) : (x + y).birthday ≤ x.birthday + y.birthday := by
  obtain ⟨a, ha, ha'⟩ := birthday_eq_iGameBirthday x
  obtain ⟨b, hb, hb'⟩ := birthday_eq_iGameBirthday y
  rw [← ha', ← hb', ← ha, ← hb, ← IGame.birthday_add]
  exact birthday_mk_le _

theorem birthday_sub_le (x y : Game) : (x - y).birthday ≤ x.birthday + y.birthday := by
  simpa using birthday_add_le x (-y)

/- The bound `(x * y).birthday ≤ x.birthday * y.birthday` on surreals is currently an open problem.
See https://mathoverflow.net/a/476829/147705. -/

/-- Games with a bounded birthday form a small set. -/
instance small_setOf_birthday_le (o : NatOrdinal.{u}) : Small.{u} {x // birthday x ≤ o} := by
  have : Small.{u} (mk '' {x | IGame.birthday x ≤ o}) :=
    @small_image _ _ _ _ (IGame.small_setOf_birthday_le o)
  refine @small_subset _ _ _ ?_ this
  change {x | birthday x ≤ o} ⊆ mk '' {x | IGame.birthday x ≤ o}
  intro x hx
  obtain ⟨y, hy, hy'⟩ := birthday_eq_iGameBirthday x
  use y
  simp_all

/-- Games with a bounded birthday form a small set. -/
instance small_setOf_birthday_lt (o : NatOrdinal.{u}) : Small.{u} {x // birthday x < o} := by
  apply @small_subset _ _ _ _ (small_setOf_birthday_le o)
  exact fun x (hx : x.birthday < _) ↦ le_of_lt hx

end Game
