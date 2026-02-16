/-
Copyright (c) 2025 Violeta Hernández Palacios, Aaron Liu, and Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Aaron Liu, Junyan Xu
-/
import CombinatorialGames.Game.Basic
import CombinatorialGames.Game.Loopy.IGame

/-!
# Outcomes of loopy games

We define when a loopy game is a win, a draw, or a loss with each player going first
(under the normal play convention).
-/

namespace LGame
variable {p : Player} {x y : LGame}

mutual
  /-- `IsWin p x` means that player `p` wins `x` going first. -/
  inductive IsWin : Player → LGame → Prop where
    | intro {p : Player} {x y : LGame} : y ∈ x.moves p → IsLoss (-p) y → IsWin p x
  /-- `IsLoss p x` means that player `p` loses `x` going first. -/
  inductive IsLoss : Player → LGame → Prop where
    | intro {p : Player} {x : LGame} : (∀ y ∈ x.moves p, IsWin (-p) y) → IsLoss p x
end

theorem isWin_iff_exists : IsWin p x ↔ ∃ y ∈ x.moves p, IsLoss (-p) y where
  mp h := h.rec (motive_2 := fun _ _ _ ↦ True) (fun hyx hy _ ↦ ⟨_, hyx, hy⟩) fun _ _ ↦ ⟨⟩
  mpr := fun ⟨_, hyx, hy⟩ ↦ .intro hyx hy

theorem isLoss_iff_forall : IsLoss p x ↔ ∀ y ∈ x.moves p, IsWin (-p) y where
  mp h := h.rec (motive_1 := fun _ _ _ ↦ True) (fun _ _ _ ↦ ⟨⟩) fun h _ ↦ h
  mpr := .intro

theorem IsLoss.isWin_of_mem_moves (h : IsLoss p x) (hy : y ∈ x.moves p) : IsWin (-p) y :=
  isLoss_iff_forall.1 h y hy

theorem not_isWin_iff_forall : ¬ IsWin p x ↔ ∀ y ∈ x.moves p, ¬ IsLoss (-p) y := by
  simp [isWin_iff_exists]

theorem not_isLoss_iff_exists : ¬ IsLoss p x ↔ ∃ y ∈ x.moves p, ¬ IsWin (-p) y := by
  simp [isLoss_iff_forall]

/-- A surviving strategy for player `p`, going second.

This is a set of states, such that for every move the opposite player makes, `p` can bring it back
to the set.

You can think of this as a nonconstructive version of the more common definition of a strategy,
which gives an explicit answer for every reachable state. -/
def IsStrategy (p : Player) (s : Set LGame) : Prop :=
  ∀ y ∈ s, ∀ z ∈ y.moves (-p), ∃ r ∈ z.moves p, r ∈ s

theorem IsStrategy.neg {s : Set LGame} (h : IsStrategy p s) : IsStrategy (-p) (-s) := by
  aesop (add simp [IsStrategy])

@[simp]
theorem isStrategy_neg {s : Set LGame} : IsStrategy p (-s) ↔ IsStrategy (-p) s := by
  constructor <;> intro h <;> simpa using h.neg

theorem IsStrategy.iUnion {ι} {s : ι → Set LGame} (h : ∀ i, IsStrategy p (s i)) :
    IsStrategy p (⋃ i, s i) :=
  fun y hy z hz ↦ have ⟨i, hi⟩ := Set.mem_iUnion.mp hy
    have ⟨r, hrz, hr⟩ := h i y hi z hz
    ⟨r, hrz, Set.mem_iUnion_of_mem i hr⟩

theorem IsStrategy.sUnion {S : Set (Set LGame)} (h : ∀ s ∈ S, IsStrategy p s) :
    IsStrategy p (⋃₀ S) :=
  Set.sUnion_eq_iUnion ▸ .iUnion fun s ↦ h s s.2

theorem isStrategy_setOf_isLoss (p : Player) : IsStrategy p {x | IsLoss (-p) x} :=
  fun _ ↦ (isLoss_iff_forall.trans (by simp [isWin_iff_exists])).mp

theorem isStrategy_setOf_not_isWin (p : Player) : IsStrategy p {x | ¬ IsWin (-p) x} :=
  fun x hx ↦ by
    simp_rw [Set.mem_setOf, isWin_iff_exists, isLoss_iff_forall] at hx
    simpa using hx

theorem not_isWin_iff_mem_isStrategy : ¬ IsWin p x ↔ ∃ s, x ∈ s ∧ IsStrategy (-p) s where
  mp h := ⟨_, by simpa, isStrategy_setOf_not_isWin _⟩
  mpr ls ll := ll.rec (motive_2 := fun _ _ _ ↦ _) (@fun p x y hyx _ hy ⟨s, hx, hs⟩ ↦
    have hp := (neg_neg p).symm
    have ⟨r, hr⟩ := hs x hx y (hp ▸ hyx); hy r hr.1 ⟨s, hr.2, hp ▸ hs⟩) (fun _ ↦ id) ls

theorem IsStrategy.not_isWin' {s} (h : IsStrategy (-p) s) (hx : x ∈ s) : ¬ IsWin p x := by
  rw [not_isWin_iff_mem_isStrategy]
  use s

theorem IsStrategy.not_isWin {s} (h : IsStrategy p s) (hx : x ∈ s) : ¬ IsWin (-p) x := by
  rw [← neg_neg p] at h
  exact h.not_isWin' hx

@[simp]
theorem not_isLoss_of_isWin (h : IsWin p x) : ¬ IsLoss p x :=
  fun h' ↦ not_isWin_iff_mem_isStrategy.mpr ⟨_, h', by simpa using isStrategy_setOf_isLoss (-p)⟩ h

@[simp]
theorem not_isWin_of_isLoss (h : IsLoss p x) : ¬ IsWin p x :=
  imp_not_comm.1 not_isLoss_of_isWin h

@[simp]
theorem isWin_neg : IsWin p (-x) ↔ IsWin (-p) x := by
  rw [← not_iff_not, not_isWin_iff_mem_isStrategy, not_isWin_iff_mem_isStrategy,
    (Equiv.neg _).exists_congr_left]
  simp [← isStrategy_neg]

theorem IsWin.neg (h : IsWin p x) : IsWin (-p) (-x) := by
  rw [← neg_neg p] at h
  exact isWin_neg.2 h

@[simp]
theorem isLoss_neg : IsLoss p (-x) ↔ IsLoss (-p) x := by
  simp [isLoss_iff_forall]

theorem IsLoss.neg (h : IsLoss p x) : IsLoss (-p) (-x) := by
  rw [← neg_neg p] at h
  exact isLoss_neg.2 h

/-- `IsDraw p x` means that `p` draws `x` going first. -/
def IsDraw (p : Player) (x : LGame) : Prop := ¬ IsWin p x ∧ ¬ IsLoss p x

@[simp] theorem IsDraw.not_isWin (h : IsDraw p x) : ¬ IsWin p x := h.1
@[simp] theorem IsDraw.not_isLoss (h : IsDraw p x) : ¬ IsLoss p x := h.2
theorem not_isDraw_iff : ¬ IsDraw p x ↔ IsWin p x ∨ IsLoss p x := by rw [IsDraw]; tauto

@[simp]
theorem isDraw_neg : IsDraw p (-x) ↔ IsDraw (-p) x := by
  simp [IsDraw]

theorem IsDraw.neg (h : IsDraw p x) : IsDraw (-p) (-x) := by
  rw [← neg_neg p] at h
  exact isDraw_neg.2 h

theorem isStrategy_sub_self : IsStrategy p (.range fun x ↦ x - x) := by
  simp_rw [sub_eq_add_neg, IsStrategy, Set.forall_mem_range, forall_moves_add, exists_moves_add]
  refine fun x ↦ ⟨fun y hy ↦ .inr ⟨-y, ?_⟩, fun y hy ↦ .inl ⟨-y, ?_⟩⟩
  · simpa
  · simp_all [add_comm]

theorem not_isWin_sub_self (p : Player) (x : LGame) : ¬ IsWin p (x - x) :=
  isStrategy_sub_self.not_isWin' (by simp)

theorem outcome_trichotomy (p : Player) (x : LGame) : IsWin p x ∨ IsDraw p x ∨ IsLoss p x := by
  rw [IsDraw]; tauto

open Classical in
/-- `outcomeFor p x` is the outcome of `x` with `p` going first. -/
noncomputable def outcomeFor (p : Player) (x : LGame) : Outcome :=
  if IsWin p x then .win else if IsLoss p x then .loss else .draw

@[simp]
theorem outcomeFor_eq_win_iff : outcomeFor p x = .win ↔ IsWin p x := by
  aesop (add simp [outcomeFor])

@[simp]
theorem outcomeFor_eq_loss_iff : outcomeFor p x = .loss ↔ IsLoss p x := by
  aesop (add simp [outcomeFor])

@[simp]
theorem outcomeFor_eq_draw_iff : outcomeFor p x = .draw ↔ IsDraw p x := by
  aesop (add simp [outcomeFor, IsDraw])

@[simp]
theorem outcomeFor_neg : outcomeFor p (-x) = outcomeFor (-p) x := by
  aesop (add simp [outcomeFor])

theorem StopperFor.not_isDraw (h : StopperFor p x) : ¬ IsDraw p x :=
  h.rec fun _h IH ⟨hw, hl⟩ ↦
    have ⟨y, hyx, hy⟩ := not_isLoss_iff_exists.mp hl
    have ⟨_, hzy, hz⟩ := not_isLoss_iff_exists.mp (not_isWin_iff_forall.mp hw y hyx)
    hz <| ((not_isDraw_iff.1 <| IH y hyx).resolve_left hy).isWin_of_mem_moves hzy

theorem Stopper.not_isDraw (p : Player) (h : Stopper x) : ¬ IsDraw p x :=
  (h p).not_isDraw

instance : Preorder LGame where
  le x y := ∀ z,
    (x + z).outcomeFor left ≤ (y + z).outcomeFor left ∧
    (y + z).outcomeFor right ≤ (x + z).outcomeFor right
  le_refl := by simp
  le_trans x y z h₁ h₂ w := ⟨(h₁ _).1.trans (h₂ _).1, (h₂ _).2.trans (h₁ _).2⟩

theorem le_def : x ≤ y ↔ ∀ z,
    (x + z).outcomeFor left ≤ (y + z).outcomeFor left ∧
    (y + z).outcomeFor right ≤ (x + z).outcomeFor right :=
  .rfl

theorem outcomeFor_left_le_of_le (h : x ≤ y) (z : LGame) :
    (x + z).outcomeFor left ≤ (y + z).outcomeFor left :=
  (h z).1

theorem outcomeFor_right_le_of_le (h : x ≤ y) (z : LGame) :
    (y + z).outcomeFor right ≤ (x + z).outcomeFor right :=
  (h z).2

theorem isWin_left_add_mono (z : LGame) : Monotone fun x ↦ IsWin left (x + z) := by
  intro x y h h'
  rw [← outcomeFor_eq_win_iff] at h' ⊢
  have := h' ▸ (outcomeFor_left_le_of_le h z)
  simpa using this

theorem isWin_right_add_anti (z : LGame) : Antitone fun x ↦ IsWin right (x + z) := by
  intro x y h h'
  rw [← outcomeFor_eq_win_iff] at h' ⊢
  have := h' ▸ (outcomeFor_right_le_of_le h z)
  simpa using this

theorem not_isWin_right_sub_of_le (h : x ≤ y) : ¬ IsWin right (y - x) :=
  fun h' ↦ not_isWin_sub_self _ _ <| isWin_right_add_anti (-x) h h'

theorem not_isWin_left_sub_of_le (h : x ≤ y) : ¬ IsWin left (x - y) := by
  rw [← neg_sub, isWin_neg]; exact not_isWin_right_sub_of_le h

theorem equiv_def : x ≈ y ↔ ∀ p z,
    (x + z).outcomeFor p = (y + z).outcomeFor p := by
  grind [AntisymmRel, le_def]

theorem le_iff_of_stopper (hx : Stopper x) (hy : Stopper y) : x ≤ y ↔ ¬ IsWin right (y - x) where
  mp := not_isWin_right_sub_of_le
  mpr h z := by
    constructor
    · cases h' : outcomeFor left (x + z) with
      | loss => simp
      | draw => sorry
      | win => sorry
    · sorry

theorem le_iff_of_stopper' (hx : Stopper x) (hy : Stopper y) : x ≤ y ↔ ¬ IsWin left (x - y) := by
  rw [← neg_sub, isWin_neg, le_iff_of_stopper hx hy, Player.neg_left]

/-! ### Outcome calculations -/

/-! #### dud -/

theorem isStrategy_dud (p : Player) : IsStrategy p {dud} := by
  simp [IsStrategy]

theorem isDraw_dud (p : Player) : IsDraw p dud := by
  have H (p) : ¬ IsWin p dud := (isStrategy_dud _).not_isWin' (by simp)
  use H _
  rw [not_isLoss_iff_exists]
  use dud
  simpa using H _

@[simp]
theorem outcomeFor_dud (p : Player) : outcomeFor p dud = .draw := by
  simpa using isDraw_dud p

/-! #### on -/

theorem isLoss_right_on : IsLoss right on := by
  rw [isLoss_iff_forall]
  simp

theorem isWin_left_on : IsWin left on := by
  rw [isWin_iff_exists]
  simpa using isLoss_right_on

@[simp]
theorem outcomeFor_left_on : outcomeFor left on = .win := by
  simpa using isWin_left_on

@[simp]
theorem outcomeFor_right_on : outcomeFor right on = .loss := by
  simpa using isLoss_right_on

/-! #### off -/

theorem isLoss_left_off : IsLoss left off := by
  rw [← neg_on, isLoss_neg]
  exact isLoss_right_on

theorem isWin_right_off : IsWin right off := by
  rw [← neg_on, isWin_neg]
  exact isWin_left_on

@[simp]
theorem outcomeFor_left_off : outcomeFor left off = .loss := by
  simpa using isLoss_left_off

@[simp]
theorem outcomeFor_right_off : outcomeFor right off = .win := by
  simpa using isWin_right_off

/-! #### tis and tisn -/

theorem isStrategy_tis (p : Player) : IsStrategy p {tis} := by
  cases p <;> simp [IsStrategy]

theorem isStrategy_tisn (p : Player) : IsStrategy p {tisn} := by
  cases p <;> simp [IsStrategy]

theorem isLoss_right_tis : IsLoss right tis := by
  rw [isLoss_iff_forall]
  simp

theorem isLoss_left_tisn : IsLoss left tisn := by
  rw [isLoss_iff_forall]
  simp

theorem not_isWin_tis (p : Player) : ¬ IsWin p tis := (isStrategy_tis _).not_isWin' (by simp)
theorem not_isWin_tisn (p : Player) : ¬ IsWin p tisn := (isStrategy_tisn _).not_isWin' (by simp)

theorem isDraw_left_tis : IsDraw left tis := by
  use not_isWin_tis _
  rw [not_isLoss_iff_exists]
  simpa using not_isWin_tisn _

theorem isDraw_right_tisn : IsDraw right tisn := by
  use not_isWin_tisn _
  rw [not_isLoss_iff_exists]
  simpa using not_isWin_tis _

@[simp]
theorem outcomeFor_left_tis : outcomeFor left tis = .draw := by
  simpa using isDraw_left_tis

@[simp]
theorem outcomeFor_right_tis : outcomeFor right tis = .loss := by
  simpa using isLoss_right_tis

@[simp]
theorem outcomeFor_left_tisn : outcomeFor left tisn = .loss := by
  simpa using isLoss_left_tisn

@[simp]
theorem outcomeFor_right_tisn : outcomeFor right tisn = .draw := by
  simpa using isDraw_right_tisn

end LGame

/-! ### Outcomes of well-founded games -/

namespace IGame
variable {x y : IGame}

open LGame

@[simp]
theorem not_isDraw (p : Player) (x : IGame) : ¬ IsDraw p x :=
  (stopper_toLGame x).not_isDraw p

private theorem win_loss_iff :
    ((IsWin left x ↔ 0 ⧏ x) ∧ (IsLoss left x ↔ x ≤ 0)) ∧
    ((IsWin right x ↔ x ⧏ 0) ∧ (IsLoss right x ↔ 0 ≤ x)) :=
  x.moveRecOn fun x h ↦ by
    rw [isWin_iff_exists, isLoss_iff_forall, isWin_iff_exists, isLoss_iff_forall,
      zero_lf, lf_zero, le_zero, zero_le, moves_toLGame, moves_toLGame]
    simp_rw [Set.forall_mem_image, Set.exists_mem_image]
    constructor <;>
      refine ⟨exists_congr fun y ↦ and_congr_right fun hy ↦ ?_, forall₂_congr fun y hy ↦ ?_⟩
    exacts [(h _ y hy).2.2, (h _ y hy).2.1, (h _ y hy).1.2, (h _ y hy).1.1]

@[simp] theorem isWin_left_iff_zero_lf : IsWin left x ↔ 0 ⧏ x := win_loss_iff.1.1
@[simp] theorem isLoss_left_iff_le_zero : IsLoss left x ↔ x ≤ 0 := win_loss_iff.1.2
@[simp] theorem isWin_right_iff_lf_zero : IsWin right x ↔ x ⧏ 0 := win_loss_iff.2.1
@[simp] theorem isLoss_right_iff_zero_le : IsLoss right x ↔ 0 ≤ x := win_loss_iff.2.2

theorem fuzzy_zero_iff_isWin : x ‖ 0 ↔ ∀ p, IsWin p x := by simp [IncompRel]
theorem equiv_zero_iff_isLoss : x ≈ 0 ↔ ∀ p, IsLoss p x := by simp [AntisymmRel]

theorem lt_zero_iff_isLoss_and_isWin : x < 0 ↔ IsLoss left x ∧ IsWin right x := by
  simp [lt_iff_le_not_ge]

theorem zero_lt_iff_isWin_and_isLoss : 0 < x ↔ IsWin left x ∧ IsLoss right x := by
  simp [lt_iff_le_not_ge, and_comm]

@[simp]
theorem toLGame_le_toLGame_iff : x.toLGame ≤ y.toLGame ↔ x ≤ y := by
  rw [le_iff_of_stopper (stopper_toLGame _) (stopper_toLGame _), ← toLGame_sub,
    isWin_right_iff_lf_zero, not_not, IGame.sub_nonneg]

@[simp]
theorem toLGame_lt_toLGame_iff : x.toLGame < y.toLGame ↔ x < y := by
  simp [lt_iff_le_not_ge]

@[simp]
theorem toLGame_equiv_toLGame_iff : x.toLGame ≈ y.toLGame ↔ x ≈ y := by
  simp [AntisymmRel]

@[simp]
theorem toLGame_fuzzy_toLGame_iff : x.toLGame ‖ y.toLGame ↔ x ‖ y := by
  simp [IncompRel]

end IGame
