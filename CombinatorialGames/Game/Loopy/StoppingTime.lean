/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
import CombinatorialGames.Game.Loopy.Basic
import CombinatorialGames.Game.IGame
import CombinatorialGames.NatOrdinal.Basic
import CombinatorialGames.Mathlib.WithTop

/-!
# Stopping time

For `p q : Player` and `x : LGame.{u}`, `stoppingTime p q x : WithTop NatOrdinal.{u}` is called
the stopping time of `x`, and represents how long it will take with optimal play
for `p` for force a win if it is `q`'s turn to move on `x`.
No move by `p` can strictly decrease the stopping time, and
no move by `-p` can strictly increase the stopping time.
If `p` cannot force a win then it takes the value `⊤`, and `-p` can survive forever by
only moving to other positions whose stopping time is also `⊤`.
Otherwise it is an ordinal that strictly decreases whenever `-p` moves.
Then `p` can force a win by moving to positions with an equal stopping time.
The stopping times of the positions for `-p` will then spell out a
strictly decreasing sequence of ordinals, which must eventually reach `0`,
at which point `-p` will have no moves left.
The lemma `stoppingTime_of_eq` characterizes the behavior of `stoppingTime`
when it is `p`'s turn to move, and
the lemma `stoppingTime_of_ne` characterizes the behavior of `stoppingTime`
when it is `-p`'s turn to move.

`stoppingTime p : Player → LGame.{u} → WithTop NatOrdinal.{u}` is the unique fixed point of the map
`val ↦ (p, x ↦ ⨅ y ∈ x.moves p, val (-p) y; -p, x ↦ ⨆ y ∈ x.moves (-p), stoppingTime p y + 1)`.
It therefore satisfies both an induction and a coinduction principle,
given by `stoppingTime_induction` and `stoppingTime_coinduction`.
`stoppingTime_induction` says that any other `val : Player → LGame.{u} → WithTop NatOrdinal.{u}`
increased by this map must be smaller than `stoppingTime`, and
`stoppingTime_coinduction` says that any other `val : Player → LGame.{u} → WithTop NatOrdinal.{u}`
decreased by this map must be bigger than `stoppingTime`.

-/

universe u v

/-! ### For Mathlib -/

theorem Monotone.iInf' {α β : Type*} {ι : Sort*} [Preorder α] [CompleteLattice β] {f : ι → α → β}
    (hf : ∀ (i : ι), Monotone (f i)) : Monotone (fun x => ⨅ i, f i x) :=
  (congrArg Monotone (funext (@iInf_apply _ _ _ _ _))).mp (Monotone.iInf hf)

theorem Monotone.iSup' {α β : Type*} {ι : Sort*} [Preorder α] [CompleteLattice β] {f : ι → α → β}
    (hf : ∀ (i : ι), Monotone (f i)) : Monotone (fun x => ⨆ i, f i x) :=
  (congrArg Monotone (funext (@iSup_apply _ _ _ _ _))).mp (Monotone.iSup hf)

theorem OrderHom.lfp_le_gfp {α : Type*} [CompleteLattice α] (f : α →o α) : f.lfp ≤ f.gfp :=
  f.lfp_le_fixed f.isFixedPt_gfp

theorem Order.lt_add_one_iff_not_isMax {α : Type*} [Preorder α] [Add α] [One α] [SuccAddOrder α]
    (x : α) : x < x + 1 ↔ ¬IsMax x := by
  rw [← Order.succ_eq_add_one, Order.lt_succ_iff_not_isMax]

theorem Order.le_add_one {α : Type*} [Preorder α] [Add α] [One α] [SuccAddOrder α]
    (x : α) : x ≤ x + 1 := by
  rw [← Order.succ_eq_add_one]
  exact Order.le_succ x

noncomputable section
namespace LGame

/-- Refines the approximations for the stopping times. -/
private def stoppingTimeApprox (p : Player) : (LGame.{u} → WithTop NatOrdinal.{u}) →o
    (LGame.{u} → WithTop NatOrdinal.{u}) where
  toFun f x := ⨅ y ∈ x.moves p, ⨆ i ∈ y.moves (-p), f i + 1
  monotone' := monotone_lam fun _ =>
    Monotone.iInf' fun _ => Monotone.iInf' fun _ => Monotone.iSup' fun i => Monotone.iSup' fun _ =>
      add_left_mono.comp (Function.monotone_eval i)

private theorem eq_of_finite (p : Player) {x} (hx : stoppingTimeApprox p x = x)
    {i : LGame.{u}} (hi : (stoppingTimeApprox p).lfp i ≠ ⊤) :
    (stoppingTimeApprox p).lfp i = x i := by
  have ihx : ∀ j, (stoppingTimeApprox p).lfp j < (stoppingTimeApprox p).lfp i →
      (stoppingTimeApprox p).lfp j = x j := fun j hj =>
    eq_of_finite p hx (hj.trans (lt_top_iff_ne_top.2 hi)).ne
  have hli : ¬IsMax ((stoppingTimeApprox p).lfp i) := mt isMax_iff_eq_top.1 hi
  apply le_antisymm ((stoppingTimeApprox p).isLeast_lfp.right hx i)
  have hg : IsGLB _ (stoppingTimeApprox p (stoppingTimeApprox p).lfp i) := isGLB_biInf
  rw [(stoppingTimeApprox p).isFixedPt_lfp] at hg
  have hk := hg.mem_of_not_isPredPrelimit
    ((Order.not_isPredPrelimit_iff_exists_covBy _).2
      ⟨Order.succ _, Order.covBy_succ_of_not_isMax hli⟩)
  rw [Set.mem_image] at hk
  obtain ⟨u, hui, hu⟩ := hk
  rw [← hu, ← hx]
  apply iInf₂_le_of_le u hui
  apply ge_of_eq
  congr! 4 with k hk
  apply ihx
  rw [← hu]
  refine lt_of_lt_of_le ?_ (le_iSup₂ k hk)
  rw [← Order.succ_eq_add_one, Order.lt_succ_iff_not_isMax]
  refine mt (IsMax.mono · ?_) hli
  rw [← hu]
  apply le_iSup₂_of_le k hk
  rw [← Order.succ_eq_add_one]
  exact Order.le_succ _
termination_by wellFounded_lt.wrap ((stoppingTimeApprox p).lfp i)

private theorem lfp_eq_gfp (p : Player) :
    (stoppingTimeApprox p).lfp = (stoppingTimeApprox p).gfp := by
  ext i
  by_cases hi : (stoppingTimeApprox p).lfp i = ⊤
  · exact le_antisymm ((stoppingTimeApprox p).lfp_le_gfp i) (le_top.trans_eq hi.symm)
  · exact eq_of_finite p (stoppingTimeApprox p).isFixedPt_gfp hi

/-- `stoppingTime p q x` is the time it takes for `p` to force a win if `q` goes first on `x`,
counted in moves made by `-p`. -/
@[irreducible]
def stoppingTime (p q : Player) (x : LGame.{u}) : WithTop NatOrdinal.{u} :=
  if p = q then (stoppingTimeApprox p).lfp x
  else ⨆ i ∈ x.moves q, (stoppingTimeApprox p).lfp i + 1

theorem stoppingTime_of_eq {p q : Player} (h : p = q) (x : LGame.{u}) :
    stoppingTime p q x = ⨅ y ∈ x.moves q, stoppingTime p (-q) y := by
  unfold stoppingTime
  conv =>
    congr
    · rw [if_pos h, ← OrderHom.isFixedPt_lfp,
        stoppingTimeApprox, OrderHom.coe_mk, ← stoppingTimeApprox, h]
    · enter [1, y, 1, _]
      rw [if_neg (Player.ne_neg.2 h), h]

theorem stoppingTime_of_ne {p q : Player} (h : p ≠ q) (x : LGame.{u}) :
    stoppingTime p q x = ⨆ y ∈ x.moves q, stoppingTime p (-q) y + 1 := by
  unfold stoppingTime
  conv =>
    congr
    · rw [if_neg h]
    · enter [1, y, 1, _]
      rw [if_pos (Player.eq_neg_of_ne h)]

theorem stoppingTime_induction (p : Player)
    (val : Player → LGame.{u} → WithTop NatOrdinal.{u})
    (hp : ∀ x, ⨅ y ∈ x.moves p, val (-p) y ≤ val p x)
    (hnp : ∀ x, ⨆ y ∈ x.moves (-p), val p y + 1 ≤ val (-p) x) :
    stoppingTime p ≤ val := by
  have up : stoppingTimeApprox p (val p) ≤ val p :=
    fun x ↦ (iInf₂_mono fun y _ ↦ hnp y).trans (hp x)
  apply (stoppingTimeApprox p).lfp_le at up
  intro q
  unfold stoppingTime
  split_ifs with hq
  · cases hq
    exact up
  · cases Player.neg_eq_of_ne hq
    exact fun x => (iSup₂_mono fun y _ => add_left_mono (up y)).trans (hnp x)

theorem stoppingTime_coinduction (p : Player)
    (val : Player → LGame.{u} → WithTop NatOrdinal.{u})
    (hp : ∀ x, val p x ≤ ⨅ y ∈ x.moves p, val (-p) y)
    (hnp : ∀ x, val (-p) x ≤ ⨆ y ∈ x.moves (-p), val p y + 1) :
    val ≤ stoppingTime p := by
  have up : val p ≤ stoppingTimeApprox p (val p) :=
    fun x ↦ (hp x).trans (iInf₂_mono fun y _ ↦ hnp y)
  intro q
  apply (stoppingTimeApprox p).le_gfp at up
  unfold stoppingTime
  simp_rw [lfp_eq_gfp]
  split_ifs with hq
  · cases hq
    exact up
  · cases Player.neg_eq_of_ne hq
    exact fun x ↦ (hnp x).trans (iSup₂_mono fun y j ↦ add_left_mono (up y))
