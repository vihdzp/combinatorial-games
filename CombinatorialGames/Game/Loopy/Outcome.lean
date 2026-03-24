/-
Copyright (c) 2025 Violeta Hernández Palacios, Aaron Liu, and Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Aaron Liu, Junyan Xu
-/
module

public import CombinatorialGames.Game.Loopy.IGame

/-!
# Outcomes of loopy games

We define when a loopy game is a win, a draw, or a loss with each player going first
(under the normal play convention).
-/

public section

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

theorem not_isWin_iff_mem_Strategy : ¬ IsWin p x ↔ ∃ s, x ∈ s ∧ IsStrategy (-p) s where
  mp h := ⟨_, by simpa, isStrategy_setOf_not_isWin _⟩
  mpr ls ll := ll.rec (motive_2 := fun _ _ _ ↦ _) (@fun p x y hyx _ hy ⟨s, hx, hs⟩ ↦
    have hp := (neg_neg p).symm
    have ⟨r, hr⟩ := hs x hx y (hp ▸ hyx); hy r hr.1 ⟨s, hr.2, hp ▸ hs⟩) (fun _ ↦ id) ls

@[simp]
theorem not_isLoss_of_isWin (h : IsWin p x) : ¬ IsLoss p x :=
  fun h' ↦ not_isWin_iff_mem_Strategy.mpr ⟨_, h', by simpa using isStrategy_setOf_isLoss (-p)⟩ h

@[simp]
theorem not_isWin_of_isLoss (h : IsLoss p x) : ¬ IsWin p x :=
  imp_not_comm.1 not_isLoss_of_isWin h

/-- `IsDraw p x` means that `p` draws `x` going first. -/
def IsDraw (p : Player) (x : LGame) : Prop := ¬ IsWin p x ∧ ¬ IsLoss p x

@[simp] theorem IsDraw.not_isWin (h : IsDraw p x) : ¬ IsWin p x := h.1
@[simp] theorem IsDraw.not_isLoss (h : IsDraw p x) : ¬ IsLoss p x := h.2
theorem not_isDraw_iff : ¬ IsDraw p x ↔ IsWin p x ∨ IsLoss p x := by rw [IsDraw]; tauto

/-- The three possible outcomes of a game. -/
inductive Outcome : Type | win | draw | loss

/-- `outcomeFor p x` is the outcome of `x` with `p` going first. -/
noncomputable def outcomeFor (p : Player) (x : LGame) : Outcome := by classical
  exact if IsWin p x then .win else if IsLoss p x then .loss else .draw

@[simp]
theorem outcomeFor_eq_win_iff : outcomeFor p x = .win ↔ IsWin p x := by
  aesop (add simp [outcomeFor])

@[simp]
theorem outcomeFor_eq_loss_iff : outcomeFor p x = .loss ↔ IsLoss p x := by
  aesop (add simp [outcomeFor])

@[simp]
theorem outcomeFor_eq_draw_iff : outcomeFor p x = .draw ↔ IsDraw p x := by
  aesop (add simp [outcomeFor, IsDraw])

theorem StopperFor.not_isDraw (h : StopperFor p x) : ¬ IsDraw p x :=
  h.rec fun _h IH ⟨hw, hl⟩ ↦
    have ⟨y, hyx, hy⟩ := not_isLoss_iff_exists.mp hl
    have ⟨_, hzy, hz⟩ := not_isLoss_iff_exists.mp (not_isWin_iff_forall.mp hw y hyx)
    hz <| ((not_isDraw_iff.1 <| IH y hyx).resolve_left hy).isWin_of_mem_moves hzy

theorem Stopper.not_isDraw (p : Player) (h : Stopper x) : ¬ IsDraw p x :=
  (h p).not_isDraw

end LGame

namespace IGame
variable {x : IGame}

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

end IGame
end
