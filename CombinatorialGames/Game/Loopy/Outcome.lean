/-
Copyright (c) 2025 Violeta Hernández Palacios, Aaron Liu, and Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Aaron Liu, Junyan Xu
-/
import CombinatorialGames.Game.Loopy.IGame

/-!
# Outcomes of loopy games

We define when a loopy game is a win, a draw, or a loss with each player going first
(under the normal play convention).
-/

namespace LGame

mutual
  /-- `IsWin p x` means that player `p` wins `x` going first. -/
  inductive IsWin : Player → LGame → Prop where
    | intro {p : Player} {x y : LGame} : y ∈ x.moves p → IsLoss (-p) y → IsWin p x
  /-- `IsLoss p x` means that player `p` loses `x` going first. -/
  inductive IsLoss : Player → LGame → Prop where
    | intro {p : Player} {x : LGame} : (∀ y ∈ x.moves p, IsWin (-p) y) → IsLoss p x
end

theorem isWin_iff_exists {p : Player} {x : LGame} : IsWin p x ↔ ∃ y ∈ x.moves p, IsLoss (-p) y where
  mp h := h.rec (motive_2 := fun _ _ _ ↦ True) (fun hyx hy _ ↦ ⟨_, hyx, hy⟩) fun _ _ ↦ ⟨⟩
  mpr := fun ⟨_, hyx, hy⟩ ↦ .intro hyx hy

theorem isLoss_iff_forall {p : Player} {x : LGame} : IsLoss p x ↔ ∀ y ∈ x.moves p, IsWin (-p) y where
  mp h := h.rec (motive_1 := fun _ _ _ ↦ True) (fun _ _ _ ↦ ⟨⟩) fun h _ ↦ h
  mpr := .intro

theorem not_isWin_iff_forall {p : Player} {x : LGame} :
    ¬ IsWin p x ↔ ∀ y ∈ x.moves p, ¬ IsLoss (-p) y := by
  simp [isWin_iff_exists]

theorem not_isLoss_iff_exists {p : Player} {x : LGame} :
    ¬ IsLoss p x ↔ ∃ y ∈ x.moves p, ¬ IsWin (-p) y := by
  simp [isLoss_iff_forall]

/-- A surviving strategy for player `p`, going second.

This is a set of states, such that for every move the opposite player makes, `p` can bring it back
to the set.

You can think of this as a nonconstructive version of the more common definition of a strategy,
which gives an explicit answer for every reachable state. -/
def IsStrategy (p : Player) (s : Set LGame) : Prop :=
  ∀ y ∈ s, ∀ z ∈ y.moves (-p), ∃ r ∈ z.moves p, r ∈ s

theorem IsStrategy.neg {p : Player} {s : Set LGame} (h : IsStrategy p s) : IsStrategy (-p) (-s) := by
  aesop (add simp [IsStrategy])

@[simp]
theorem isStrategy_neg {p : Player} {s : Set LGame} : IsStrategy p (-s) ↔ IsStrategy (-p) s := by
  constructor <;> intro h <;> simpa using h.neg

theorem IsStrategy.iUnion {p : Player} {ι} {s : ι → Set LGame} (h : ∀ i, IsStrategy p (s i)) :
    IsStrategy p (⋃ i, s i) :=
  fun y hy z hz ↦ have ⟨i, hi⟩ := Set.mem_iUnion.mp hy
    have ⟨r, hrz, hr⟩ := h i y hi z hz
    ⟨r, hrz, Set.mem_iUnion_of_mem i hr⟩

theorem IsStrategy.sUnion {p : Player} {S : Set (Set LGame)} (h : ∀ s ∈ S, IsStrategy p s) :
    IsStrategy p (⋃₀ S) :=
  Set.sUnion_eq_iUnion ▸ .iUnion fun s ↦ h s s.2

theorem isStrategy_setOf_isLoss (p : Player) : IsStrategy p {x | IsLoss (-p) x} :=
  fun _ ↦ (isLoss_iff_forall.trans (by simp [isWin_iff_exists])).mp

theorem isStrategy_setOf_not_isWin (p : Player) : IsStrategy p {x | ¬ IsWin (-p) x} :=
  fun x hx ↦ by
    simp_rw [Set.mem_setOf, isWin_iff_exists, isLoss_iff_forall] at hx
    simpa using hx

theorem not_isWin_iff_mem_Strategy {p : Player} {x : LGame} :
    ¬ IsWin p x ↔ ∃ s, x ∈ s ∧ IsStrategy (-p) s := by
  conv_lhs => rw [← neg_neg p]
  constructor
  · exact fun h ↦ ⟨_, h, isStrategy_setOf_not_isWin _⟩
  · exact fun ls ll ↦ ll.rec (motive_2 := fun _ _ _ ↦ _) (@fun p x y hyx hy ⟨s, hx, hs⟩ ↦
    have ⟨r, hr⟩ := hs x hx y (by simpa); hy r hr.1 ⟨s, hr.2, hs⟩) (fun _ ↦ id) ls

#exit

theorem not_isLeftWin_iff_mem_rightStrategy {x : LGame} :
    ¬ IsLeftWin x ↔ ∃ s, x ∈ s ∧ IsRightStrategy s where
  mp h := ⟨_, h, isRightStrategy_not_isLeftWin⟩
  mpr ls ll := ll.rec (motive_2 := fun _ _ ↦ _) (fun x y hyx _ hy ⟨s, hx, hs⟩ ↦
    have ⟨r, hr⟩ := hs x hx y hyx; hy r hr.1 ⟨s, hr.2, hs⟩) (fun _ _ ↦ id) ls

theorem not_isLeftWin_and_isLeftLoss {x : LGame} : ¬ (IsLeftWin x ∧ IsLeftLoss x) :=
  fun ⟨w, l⟩ ↦ not_isLeftWin_iff_mem_rightStrategy.mpr ⟨_, l, isRightStrategy_isLeftLoss⟩ w

theorem not_isRightWin_and_isRightLoss {x : LGame} : ¬ (IsRightWin x ∧ IsRightLoss x) :=
  fun ⟨w, l⟩ ↦ not_isRightWin_iff_mem_leftStrategy.mpr ⟨_, l, isLeftStrategy_isRightLoss⟩ w

/-- `IsLeftDraw x` means that left draws `x` going first. -/
def IsLeftDraw (x : LGame) : Prop := ¬ IsLeftWin x ∧ ¬ IsLeftLoss x

/-- `IsRightDraw x` means that right draws `x` going first. -/
def IsRightDraw (x : LGame) : Prop := ¬ IsRightWin x ∧ ¬ IsRightLoss x

/-- The three possible outcomes of a game. -/
inductive Outcome : Type | win | draw | loss

/-- `leftOutcome x` is the outcome of `x` with left going first. -/
noncomputable def leftOutcome (x : LGame) : Outcome := by classical
  exact if IsLeftWin x then .win else if IsLeftLoss x then .loss else .draw

/-- `rightOutcome x` is the outcome of `x` with right going first. -/
noncomputable def rightOutcome (x : LGame) : Outcome := by classical
  exact if IsRightWin x then .win else if IsRightLoss x then .loss else .draw

theorem leftOutcome_eq_win_iff {x : LGame} : leftOutcome x = .win ↔ IsLeftWin x := by
  classical rw [leftOutcome, Ne.ite_eq_left_iff]
  split_ifs <;> rintro ⟨_⟩

theorem rightOutcome_eq_win_iff {x : LGame} : rightOutcome x = .win ↔ IsRightWin x := by
  classical rw [rightOutcome, Ne.ite_eq_left_iff]
  split_ifs <;> rintro ⟨_⟩

theorem leftOutcome_eq_loss_iff {x : LGame} : leftOutcome x = .loss ↔ IsLeftLoss x := by
  classical rw [leftOutcome]
  split_ifs with w l
  · exact false_iff _ ▸ fun l ↦ not_isLeftWin_and_isLeftLoss ⟨w, l⟩
  all_goals simpa

theorem rightOutcome_eq_loss_iff {x : LGame} : rightOutcome x = .loss ↔ IsRightLoss x := by
  classical rw [rightOutcome]
  split_ifs with w l
  · exact false_iff _ ▸ fun l ↦ not_isRightWin_and_isRightLoss ⟨w, l⟩
  all_goals simpa

theorem leftOutcome_eq_draw_iff {x : LGame} : leftOutcome x = .draw ↔ IsLeftDraw x := by
  classical rw [leftOutcome]
  split_ifs with w l
  on_goal 3 => simpa using ⟨w, l⟩
  all_goals rw [false_iff]
  exacts [(·.1 w), (·.2 l)]

theorem rightOutcome_eq_draw_iff {x : LGame} : rightOutcome x = .draw ↔ IsRightDraw x := by
  classical rw [rightOutcome]
  split_ifs with w l
  on_goal 3 => simpa using ⟨w, l⟩
  all_goals rw [false_iff]
  exacts [(·.1 w), (·.2 l)]

/-- If there is no infinite play starting by from `x` with right going second,
then `x` cannot end in a draw with right going second. -/
-- Note: the spelling `Relation.Comp (· ∈ ·ᴿ) (· ∈ ·ᴸ)` is slightly longer
theorem not_isLeftDraw_of_acc_comp {x : LGame}
    (h : Acc (fun z x ↦ ∃ y ∈ xᴸ, z ∈ yᴿ) x) : ¬ IsLeftDraw x :=
  h.rec fun _x _ ih ⟨nw, nl⟩ ↦
    have ⟨y, hyx, hy⟩ := not_isLeftLoss_iff_exists.mp nl
    have ⟨z, hzy, hz⟩ := not_isRightLoss_iff_exists.mp (not_isLeftWin_iff_forall.mp nw y hyx)
    ih z ⟨y, hyx, hzy⟩ ⟨hz, not_isRightWin_iff_forall.mp hy z hzy⟩

/-- If there is no infinite play starting from `x` with right going first,
then `x` cannot end in a draw with right going first. -/
theorem not_isRightDraw_of_acc_comp {x : LGame}
    (h : Acc (fun z x ↦ ∃ y ∈ xᴿ, z ∈ yᴸ) x) : ¬ IsRightDraw x :=
  h.rec fun _x _ ih ⟨nw, nl⟩ ↦
    have ⟨y, hyx, hy⟩ := not_isRightLoss_iff_exists.mp nl
    have ⟨z, hzy, hz⟩ := not_isLeftLoss_iff_exists.mp (not_isRightWin_iff_forall.mp nw y hyx)
    ih z ⟨y, hyx, hzy⟩ ⟨hz, not_isLeftWin_iff_forall.mp hy z hzy⟩

theorem not_isLeftDraw_of_acc_isOption {x : LGame} (h : Acc IsOption x) : ¬ IsLeftDraw x :=
  not_isLeftDraw_of_acc_comp <| Subrelation.accessible
    (fun ⟨_, hyx, hzy⟩ ↦ .tail (.single <| .of_mem_moves hzy) (.of_mem_moves hyx)) h.transGen

theorem not_isRightDraw_of_acc_isOption {x : LGame} (h : Acc IsOption x) : ¬ IsRightDraw x :=
  not_isRightDraw_of_acc_comp <| Subrelation.accessible
    (fun ⟨_, hyx, hzy⟩ ↦ .tail (.single <| .of_mem_moves hzy) (.of_mem_moves hyx)) h.transGen

end LGame

namespace IGame

open LGame

theorem not_isLeftDraw (x : IGame) : ¬ IsLeftDraw x :=
  LGame.not_isLeftDraw_of_acc_isOption x.acc_toLGame

theorem not_isRightDraw (x : IGame) : ¬ IsRightDraw x :=
  LGame.not_isRightDraw_of_acc_isOption x.acc_toLGame

private theorem win_loss_iff {x : IGame} :
    ((IsLeftWin x ↔ 0 ⧏ x) ∧ (IsLeftLoss x ↔ x ≤ 0)) ∧
    ((IsRightWin x ↔ x ⧏ 0) ∧ (IsRightLoss x ↔ 0 ≤ x)) :=
  x.moveRecOn fun x h ↦ by
    rw [isLeftWin_iff_exists, isLeftLoss_iff_forall, isRightWin_iff_exists, isRightLoss_iff_forall,
      zero_lf, lf_zero, le_zero, zero_le, moves_toLGame, moves_toLGame]
    simp_rw [Set.forall_mem_image, Set.exists_mem_image]
    constructor <;>
      refine ⟨exists_congr fun y ↦ and_congr_right fun hy ↦ ?_, forall₂_congr fun y hy ↦ ?_⟩
    exacts [(h _ y hy).2.2, (h _ y hy).2.1, (h _ y hy).1.2, (h _ y hy).1.1]

theorem isLeftWin_iff_zero_lf {x : IGame} : IsLeftWin x ↔ 0 ⧏ x := win_loss_iff.1.1
theorem isLeftLoss_iff_le_zero {x : IGame} : IsLeftLoss x ↔ x ≤ 0 := win_loss_iff.1.2
theorem isRightWin_iff_lf_zero {x : IGame} : IsRightWin x ↔ x ⧏ 0 := win_loss_iff.2.1
theorem isRightLoss_iff_zero_le {x : IGame} : IsRightLoss x ↔ 0 ≤ x := win_loss_iff.2.2

theorem fuzzy_zero_iff_and {x : IGame} : x ‖ 0 ↔ IsLeftWin x ∧ IsRightWin x := by
  rw [IncompRel, isLeftWin_iff_zero_lf, isRightWin_iff_lf_zero]

theorem equiv_zero_iff_and {x : IGame} : x ≈ 0 ↔ IsLeftLoss x ∧ IsRightLoss x := by
  rw [AntisymmRel, isLeftLoss_iff_le_zero, isRightLoss_iff_zero_le]

theorem lt_zero_iff_and {x : IGame} : x < 0 ↔ IsLeftLoss x ∧ IsRightWin x := by
  rw [lt_iff_le_not_ge, isLeftLoss_iff_le_zero, isRightWin_iff_lf_zero]

theorem zero_lt_iff_and {x : IGame} : 0 < x ↔ IsLeftWin x ∧ IsRightLoss x := by
  rw [lt_iff_le_not_ge, isLeftWin_iff_zero_lf, isRightLoss_iff_zero_le, and_comm]

end IGame
