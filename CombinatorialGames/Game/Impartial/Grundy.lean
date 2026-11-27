/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Julia Markus Himmel, Violeta Hernández Palacios
-/
module

public import CombinatorialGames.Game.Specific.Nim

/-!
# Grundy value

The Grundy value of an impartial game is recursively defined as the least nimber not among the
Grundy values of either its left or right options. This map respects addition and multiplication.

We provide two definitions for the Grundy value. `grundyFor` is computed using either the left or
right options of the game, and is defined for all games. To make the API symmetric, we also provide
`Impartial.grundy`, which enforces that the game is impartial, and is thus equal to either of
`grundyFor left` or `grundyFor right`.

The **Sprague-Grundy** theorem `Impartial.nim_grundy_equiv` shows that any impartial game is
equivalent to a game of Nim, namely that corresponding to its Grundy value.
-/

universe u

open Nimber Set

open Pointwise in
theorem Set.neg_iUnion {α : Type*} {ι : Sort*} [Neg α] (f : ι → Set α) : -⋃ i, f i = ⋃ i, -f i :=
  preimage_iUnion

theorem Set.union_rotate {α : Type*} (a b c : Set α) : a ∪ b ∪ c = b ∪ c ∪ a := by grind
theorem Set.union_rotate' {α : Type*} (a b c : Set α) : a ∪ (b ∪ c) = b ∪ (c ∪ a) := by grind

public noncomputable section

namespace IGame

/-! ### Impartialize a game -/

/-- Turn a game impartial, by giving both players the same moves at every subposition. -/
def impartialize (x : IGame) : IGame :=
  !{fun _ ↦ ⋃ p, range fun y : x.moves p ↦ impartialize y}
termination_by x
decreasing_by igame_wf

theorem impartialize_def (x : IGame) :
    impartialize x = !{fun _ ↦ ⋃ p, impartialize '' x.moves p} := by
  rw [impartialize]
  grind

theorem moves_impartialize (x : IGame) (p : Player) :
    x.impartialize.moves p = ⋃ p, impartialize '' x.moves p := by
  rw [impartialize_def, moves_ofSets]

@[simp]
theorem forall_mem_moves_impartialize {x : IGame} {p : Player} {P : IGame → Prop} :
    (∀ y ∈ x.impartialize.moves p, P y) ↔ ∀ q, ∀ y ∈ x.moves q, P (impartialize y) := by
  rw [impartialize_def]
  aesop

@[simp]
theorem exists_mem_moves_impartialize {x : IGame} {p : Player} {P : IGame → Prop} :
    (∃ y ∈ x.impartialize.moves p, P y) ↔ ∃ q, ∃ y ∈ x.moves q, P (impartialize y) := by
  rw [impartialize_def]
  aesop

protected instance Impartial.impartialize (x : IGame) : Impartial (impartialize x) := by
  apply Impartial.mk
  · rw [impartialize_def, neg_ofSets']
    simp_rw [Set.neg_iUnion]
    congr! 4 with _ p
    ext y
    rw [mem_neg, mem_image]
    apply exists_congr
    simp_rw [and_congr_right_iff]
    intro z hz
    have := Impartial.impartialize z
    conv_lhs => rw [← neg_eq z.impartialize, neg_inj]
  · simp_rw [forall_mem_moves_impartialize]
    exact fun _ _ y hy ↦ Impartial.impartialize y
termination_by x
decreasing_by igame_wf

@[simp]
theorem Impartial.impartialize_eq (x : IGame) [Impartial x] : impartialize x = x := by
  rw [impartialize_def]
  ext p y
  simp only [← moves_congr x p, moves_ofSets, mem_iUnion, mem_image, exists_const]
  refine ⟨?_, fun hy ↦ ⟨y, hy, ?_⟩⟩
  · rintro ⟨z, hz, rfl⟩
    impartial
    rwa [Impartial.impartialize_eq]
  · impartial
    rw [Impartial.impartialize_eq]
termination_by x
decreasing_by igame_wf

theorem impartial_iff_impartialize_eq {x : IGame} : Impartial x ↔ impartialize x = x := by
  refine ⟨@Impartial.impartialize_eq x, fun hx ↦ ?_⟩
  rw [← hx]
  infer_instance

@[simp]
theorem impartialize_neg (x : IGame) : impartialize (-x) = impartialize x := by
  apply Impartial.ext left
  simp_rw [moves_impartialize, Player.iUnion_eq, moves_neg]
  rw [union_comm]
  congr 1 <;> exact image_neg_of_apply_neg_eq fun y hy ↦ impartialize_neg y
termination_by x
decreasing_by igame_wf

@[simp]
theorem impartialize_add (x y : IGame) :
    impartialize (x + y) = impartialize x + impartialize y := by
  apply Impartial.ext left
  simp only [moves_impartialize, moves_add, image_iUnion, ← iUnion_union_distrib, image_union]
  congr! 3 with p <;>
  · ext z
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      rw [impartialize_add]
      exact ⟨_, mem_image_of_mem _ hz, rfl⟩
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      dsimp
      rw [← impartialize_add]
      exact ⟨_, mem_image_of_mem _ hz, rfl⟩
termination_by (x, y)
decreasing_by igame_wf

@[simp]
theorem impartialize_sub (x y : IGame) :
    impartialize (x - y) = impartialize x - impartialize y := by
  simp [sub_eq_add_neg]

@[simp]
theorem impartialize_mul (x y : IGame) :
    impartialize (x * y) = impartialize x * impartialize y := by
  apply Impartial.ext left
  simp only [moves_impartialize, moves_mul, ← iUnion_prod, image_union, image_iUnion, iUnion_prod',
    union_self]
  simp_rw [Player.iUnion_eq, union_assoc]
  nth_rw 2 [Set.union_rotate']
  congr! <;>
  · ext z
    constructor
    · rintro ⟨_, ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩, rfl⟩
      refine ⟨⟨_, _⟩, ⟨mem_image_of_mem _ ha, mem_image_of_mem _ hb⟩, ?_⟩
      simp only [mulOption, impartialize_add, impartialize_sub]
      iterate 3 rw [impartialize_mul]
    · rintro ⟨⟨_, _⟩, ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩, rfl⟩
      refine ⟨_, ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩, ?_⟩
      simp only [mulOption, impartialize_add, impartialize_sub]
      iterate 3 rw [impartialize_mul]
termination_by (x, y)
decreasing_by igame_wf

@[simp]
theorem impartialize_mulOption (x y a b : IGame) : impartialize (mulOption x y a b) =
    mulOption x.impartialize y.impartialize a.impartialize b.impartialize := by
  simp [mulOption]

open WeaklyImpartial

/-! ### Grundy value -/

private theorem nonempty_compl_of_small {s : Set Nimber.{u}} [Small.{u} s] : (sᶜ).Nonempty :=
  nonempty_of_not_bddAbove (not_bddAbove_compl_of_small _)

/-- The left or right Grundy value of a game is recursively defined as the minimum excluded value
(the infimum of the complement) of the left or right Grundy values of its left or right options.

This is an auxiliary definition for reasoning about games not yet known to be impartial. Use
`Impartial.grundy` for an impartial game. -/
def grundyFor (p : Player) (x : IGame.{u}) : Nimber.{u} :=
  sInf (Set.range fun y : x.moves p ↦ grundyFor p y.val)ᶜ
termination_by x
decreasing_by igame_wf

theorem grundyFor_def (p) (x : IGame) : grundyFor p x = sInf (grundyFor p '' x.moves p)ᶜ := by
  rw [grundyFor, image_eq_range]

theorem le_grundyFor_iff {p : Player} {x : IGame} {o : Nimber} :
    o ≤ grundyFor p x ↔ Iio o ⊆ grundyFor p '' x.moves p := by
  rw [grundyFor_def, le_csInf_iff' nonempty_compl_of_small, ← compl_subset_compl (t := Iio o),
    subset_def]
  simp

theorem lt_grundyFor_iff {p : Player} {x : IGame} {o : Nimber} :
    o < grundyFor p x ↔ Iic o ⊆ grundyFor p '' x.moves p := by
  simpa using le_grundyFor_iff (o := Order.succ o)

theorem mem_grundyFor_image_of_lt {p : Player} {x : IGame} {o : Nimber} (h : o < grundyFor p x) :
    o ∈ grundyFor p '' x.moves p :=
  le_grundyFor_iff.1 le_rfl h

theorem grundyFor_le_of_notMem {p : Player} {x : IGame} {o : Nimber}
    (h : o ∉ grundyFor p '' x.moves p) :
    grundyFor p x ≤ o :=
  le_of_not_gt <| mt mem_grundyFor_image_of_lt h

theorem grundyFor_ne {p : Player} {x y : IGame} (hy : y ∈ x.moves p) :
    grundyFor p y ≠ grundyFor p x := by
  conv_rhs => rw [grundyFor_def]
  have := csInf_mem (nonempty_compl_of_small (s := grundyFor p '' x.moves p))
  simp_all

@[simp]
theorem grundyFor_add (p : Player) (x y : IGame) :
    (x + y).grundyFor p = x.grundyFor p + y.grundyFor p := by
  apply le_antisymm
  · apply grundyFor_le_of_notMem
    rw [moves_add]
    rintro ⟨_, (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩), ha'⟩
    · rw [grundyFor_add, add_left_inj] at ha'
      exact grundyFor_ne ha ha'
    · rw [grundyFor_add, add_right_inj] at ha'
      exact grundyFor_ne ha ha'
  · rw [le_grundyFor_iff]
    intro a ha
    obtain ha | ha := Nimber.lt_add_cases ha
    · obtain ⟨z, hz, hz'⟩  := mem_grundyFor_image_of_lt ha
      refine ⟨_, add_right_mem_moves_add hz y, ?_⟩
      rw [grundyFor_add, hz', add_cancel_right]
    · obtain ⟨z, hz, hz'⟩  := mem_grundyFor_image_of_lt ha
      refine ⟨_, add_left_mem_moves_add hz x, ?_⟩
      rw [grundyFor_add, hz', add_comm, add_cancel_right]
termination_by (x, y)
decreasing_by igame_wf

@[simp]
theorem grundyFor_neg (p : Player) (x : IGame) : grundyFor p (-x) = grundyFor (-p) x := by
  rw [grundyFor_def, grundyFor_def, moves_neg]
  congr 2
  exact image_neg_of_apply_neg_eq fun _ _ ↦ grundyFor_neg p _
termination_by x
decreasing_by igame_wf

open Pointwise in
@[simp]
theorem grundyFor_image_neg (p : Player) (s : Set IGame) :
    grundyFor p '' (-s) = grundyFor (-p) '' s :=
  image_neg_of_apply_neg_eq fun _ _ ↦ grundyFor_neg _ _

@[simp]
theorem grundyFor_sub (p : Player) (x y : IGame) :
    (x - y).grundyFor p = x.grundyFor p + y.grundyFor (-p) := by
  rw [sub_eq_add_neg, grundyFor_add, grundyFor_neg]

/--
The Grundy value of an impartial game is recursively defined as the minimum excluded value
(the infimum of the complement) of the Grundy values of its options.

This definition enforces that `x` is (weakly) impartial. If you want to talk about the left or right
Grundy values of a game (e.g. if you don't yet know it to be impartial), use `grundyFor`.

The lemma `grundyFor_eq_grundy` shows that both definitions match in the case of an impartial game.
-/
@[nolint unusedArguments]
def grundy (x : IGame) [WeaklyImpartial x] : Nimber :=
  x.grundyFor right

/-- The **Sprague-Grundy theorem** states that every impartial game is equivalent to a game of nim,
namely the game of nim for the game's Grundy value. -/
theorem nim_grundy_equiv (x : IGame) [WeaklyImpartial x] : nim (grundy x) ≈ x := by
  rw [equiv_iff_forall_fuzzy default]
  constructor <;> intro y hy
  · rw [moves_nim] at hy
    obtain ⟨o, ho, rfl⟩ := hy
    obtain ⟨z, hz, rfl⟩ := mem_grundyFor_image_of_lt ho
    weakly_impartial
    rw [← grundy, (nim_grundy_equiv _).incompRel_congr_left]
    exact fuzzy_of_mem_moves hz
  · weakly_impartial
    rw [← (nim_grundy_equiv _).incompRel_congr_right, nim_fuzzy_iff]
    exact (grundyFor_ne hy).symm
termination_by x
decreasing_by igame_wf

theorem grundy_eq_iff_equiv_nim {x : IGame} [WeaklyImpartial x] {o : Nimber} :
    grundy x = o ↔ x ≈ nim o := by
  rw [← (nim_grundy_equiv x).antisymmRel_congr_left, nim_equiv_iff]

alias ⟨_, grundy_eq⟩ := grundy_eq_iff_equiv_nim

theorem grundy_eq_zero_iff {x : IGame} [WeaklyImpartial x] : grundy x = 0 ↔ x ≈ 0 := by
  simpa using grundy_eq_iff_equiv_nim (o := 0)

@[simp]
theorem grundy_eq_iff_equiv {x y : IGame} [WeaklyImpartial x] [WeaklyImpartial y] :
    grundy x = grundy y ↔ x ≈ y := by
  rw [grundy_eq_iff_equiv_nim, (nim_grundy_equiv _).antisymmRel_congr_right]

alias ⟨_, grundy_congr⟩ := grundy_eq_iff_equiv

@[simp] theorem grundy_nim (o : Nimber) : grundy (nim o) = o := grundy_eq .rfl
@[simp] theorem grundy_zero : grundy 0 = 0 := by simpa using grundy_nim 0
@[simp] theorem grundy_star : grundy ⋆ = 1 := by simpa using grundy_nim 1

@[simp]
theorem grundy_neg (x : IGame) [WeaklyImpartial x] : grundy (-x) = grundy x := by
  rw [grundy_eq_iff_equiv_nim, ← Impartial.neg_eq (nim _), IGame.neg_equiv_neg_iff,
    ← grundy_eq_iff_equiv_nim]

@[simp]
theorem grundyFor_eq_grundy (p) (x : IGame) [WeaklyImpartial x] : grundyFor p x = grundy x := by
  cases p with
  | left => rw [← grundy_neg, grundy, grundyFor_neg, Player.neg_right]
  | right => rfl

@[simp]
theorem grundy_add (x y : IGame) [WeaklyImpartial x] [WeaklyImpartial y] :
    grundy (x + y) = grundy x + grundy y :=
  grundyFor_add _ x y

theorem _root_.IGame.nim_add_equiv (a b : Nimber) : nim a + nim b ≈ nim (a + b) := by
  conv_rhs => rw [← grundy_nim a, ← grundy_nim b, ← grundy_add]
  exact (nim_grundy_equiv _).symm

theorem grundy_moves_ne {p : Player} {x y : IGame} [WeaklyImpartial x] (hy : y ∈ x.moves p) :
    haveI := WeaklyImpartial.of_mem_moves hy; grundy y ≠ grundy x := by
  cases p with
  | left =>
    simp_rw [← grundyFor_eq_grundy left]
    exact grundyFor_ne hy
  | right =>
    exact grundyFor_ne hy

/-- A more general version of `grundyFor_def`. -/
theorem grundy_eq_sInf_compl_grundyFor {x : IGame} {p q : Player} [WeaklyImpartial x] :
    grundy x = sInf (grundyFor p '' x.moves q)ᶜ := by
  rw [← grundyFor_eq_grundy q, grundyFor_def]
  congr 2
  ext y
  constructor <;>
  · rintro ⟨y, hy, rfl⟩
    weakly_impartial
    rw [grundyFor_eq_grundy, ← grundyFor_eq_grundy]
    exact mem_image_of_mem _ hy

private theorem sInf_compl_union_of_eq {s t : Set Nimber.{u}} [Small.{u} s] [Small.{u} t]
    (hst : sInf sᶜ = sInf tᶜ) : sInf (s ∪ t)ᶜ = sInf sᶜ := by
  apply le_antisymm
  · apply csInf_le'
    rw [compl_sup]
    exact ⟨csInf_mem nonempty_compl_of_small, hst ▸ csInf_mem nonempty_compl_of_small⟩
  · apply csInf_le'
    have := csInf_mem (nonempty_compl_of_small (s := s ∪ t))
    grind

theorem WeaklyImpartial.impartialize_equiv (x : IGame) [WeaklyImpartial x] :
    impartialize x ≈ x := by
  rw [← grundy_eq_iff_equiv, ← grundyFor_eq_grundy left, ← grundyFor_eq_grundy left,
    grundyFor_def, grundyFor_def, moves_impartialize]
  have H : grundyFor left '' ⋃ p, impartialize '' moves p x = grundyFor left '' ⋃ p, moves p x := by
    ext y
    simp only [mem_image, mem_iUnion]
    constructor
    · rintro ⟨_, ⟨p, y, hy, rfl⟩, rfl⟩
      refine ⟨_, ⟨p, hy⟩, ?_⟩
      weakly_impartial
      simpa using (WeaklyImpartial.impartialize_equiv y).symm
    · rintro ⟨y, ⟨p, hy⟩, rfl⟩
      refine ⟨_, ⟨p, y, hy, rfl⟩, ?_⟩
      weakly_impartial
      simpa using WeaklyImpartial.impartialize_equiv y
  rw [H, image_iUnion, Player.iUnion_eq]
  apply sInf_compl_union_of_eq
  rw [← grundyFor_def, grundyFor_eq_grundy, grundy_eq_sInf_compl_grundyFor]
termination_by x
decreasing_by igame_wf

private theorem of_grundyFor_left_eq_grundyFor_right' {x : IGame}
    (h : ∀ p, ∀ y ∈ x.moves p, WeaklyImpartial y)
    (H : grundyFor left x = grundyFor right x) : nim (grundyFor right x) ≈ x := by
  constructor <;> refine le_iff_forall_lf.2 ⟨?_, ?_⟩
  · rw [forall_mem_moves_nim]
    intro a ha
    rw [← H] at ha
    obtain ⟨y, hy, rfl⟩ := mem_grundyFor_image_of_lt ha
    have := h left y hy
    rw [grundyFor_eq_grundy]
    exact lf_of_le_left (nim_grundy_equiv y).le hy
  · intro y hy
    have := h right y hy
    grw [← nim_grundy_equiv y]
    rw [NegSelfEquiv.lf_iff_fuzzy, nim_fuzzy_iff, ← grundyFor_eq_grundy right]
    exact (grundyFor_ne hy).symm
  · intro y hy
    have := h left y hy
    grw [← nim_grundy_equiv y]
    rw [NegSelfEquiv.lf_iff_fuzzy, nim_fuzzy_iff, ← grundyFor_eq_grundy left]
    exact H ▸ grundyFor_ne hy
  · rw [forall_mem_moves_nim]
    intro a ha
    obtain ⟨y, hy, rfl⟩ := mem_grundyFor_image_of_lt ha
    have := h right y hy
    exact lf_of_right_le (nim_grundy_equiv y).ge hy

/-- If a game `x` has only weakly impartial options, and its left Grundy value equals its
right Grundy value, then it's weakly impartial. -/
theorem WeaklyImpartial.of_grundyFor_left_eq_grundyFor_right {x : IGame}
    (h : ∀ p, ∀ y ∈ x.moves p, WeaklyImpartial y)
    (H : grundyFor left x = grundyFor right x) : WeaklyImpartial x :=
  have H := of_grundyFor_left_eq_grundyFor_right' h H
  .mk ((neg_congr H).symm.trans ((Impartial.neg_eq (nim _)).symm ▸ H)) h

end IGame
end
