/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
import CombinatorialGames.Game.Loopy.Basic
import CombinatorialGames.Game.IGame
import CombinatorialGames.NatOrdinal

/-!
# Stopping time

The stopping time of a game is an ordinal which denotes how long the opponent can prolong the game.
Each game has four stopping times, the left and right stopping time for left and right going first.

- `stoppingTimeLeftLeft x`: the time it takes for left to force a win going first on `x`.
  If left cannot force a win, then the stopping time is `⊤`. It is equal to
  `⨅ y ∈ x.leftMoves, stoppingTimeLeftRight y`, which is the stopping time of
  left's best option (the one that stops the fastest).
- `stoppingTimeLeftRight x`: the time it takes for right to lose going first on `x`.
  If right can survive forever, then the stopping time is `⊤`. It is equal to
  `⨆ y ∈ x.rightMoves, stoppingTimeLeftLeft y + 1`, which is the supremum of the stopping times of
  all of right's options, plus one (since right makes a move).
- `stoppingTimeRightLeft x`: the time it takes for left to lose going first on `x`.
  If left can survive forever, then the stopping time is `⊤`. It is equal to
  `⨆ y ∈ x.leftMoves, stoppingTimeRightRight y + 1`, which is the supremum of the stopping times of
  all of left's options, plus one (since left makes a move).
- `stoppingTimeRightRight x`: the time it takes for right to force a win going first on `x`.
  If right cannot force a win, then the stopping time is `⊤`. It is equal to
  `⨅ y ∈ x.rightMoves, stoppingTimeRightLeft y`, which is the stopping time of
  right's best option (the one that stops the fastest).

These stopping times satisfy both an induction principle and a coinduction principle.

For left stopping times,
- `stoppingTimeLeft_induction left right`: if `left` and `right` are approximations to
  `stoppingTimeLeftLeft` and `stoppingTimeLeftRight` assigning to each `LGame` a
  `WithTop NatOrdinal`, and the inequalities `⨅ y ∈ x.leftMoves, right y ≤ left x` and
  `⨆ y ∈ x.rightMoves, left y + 1 ≤ right x` hold for all `x` (the pair `(left, right)` is
  *larger* then its refinement), then `left` and `right` are *overapproximations*
  to `stoppingTimeLeftLeft` and `stoppingTimeLeftRight`.
- `stoppingTimeLeft_coinduction left right`: if `left` and `right` are approximations to
  `stoppingTimeLeftLeft` and `stoppingTimeLeftRight` assigning to each `LGame` a
  `WithTop NatOrdinal`, and the inequalities `left x ≤ ⨅ y ∈ x.leftMoves, right y` and
  `right x ≤ ⨆ y ∈ x.rightMoves, left y + 1` hold for all `x` (the pair `(left, right)` is
  *smaller* then its refinement), then `left` and `right` are *underapproximations*
  to `stoppingTimeLeftLeft` and `stoppingTimeLeftRight`.
The function `(left, right) ↦ (x ↦ ⨅ y ∈ x.leftMoves, right y, x ↦ ⨆ y ∈ x.rightMoves, left y + 1)`,
is interpreted as *refining* the approximation `(left, right)` to more closely match
`(stoppingTimeLeftLeft, stoppingTimeLeftRight)` (which is its only fixpoint).
The induction principle says that if this refinement decreases the pair, it must be an
overestimation, and the coinduction principle says that if this refinement increases the pair,
it must be an underestimation.

For right stopping times,
- `stoppingTimeRight_induction left right`: if `left` and `right` are approximations to
  `stoppingTimeRightLeft` and `stoppingTimeRightRight` assigning to each `LGame` a
  `WithTop NatOrdinal`, and the inequalities `⨆ y ∈ x.leftMoves, right y + 1 ≤ left x` and
  `⨅ y ∈ x.rightMoves, left y ≤ right x` hold for all `x` (the pair `(left, right)` is
  *larger* then its refinement), then `left` and `right` are *overapproximations*
  to `stoppingTimeLeftLeft` and `stoppingTimeLeftRight`.
- `stoppingTimeRight_coinduction left right`: if `left` and `right` are approximations to
  `stoppingTimeRightLeft` and `stoppingTimeRightRight` assigning to each `LGame` a
  `WithTop NatOrdinal`, and the inequalities `left x ≤ ⨆ y ∈ x.leftMoves, right y + 1` and
  `right x ≤ ⨅ y ∈ x.rightMoves, left y` hold for all `x` (the pair `(left, right)` is
  *smaller* then its refinement), then `left` and `right` are *underapproximations*
  to `stoppingTimeLeftLeft` and `stoppingTimeLeftRight`.
The function `(left, right) ↦ (x ↦ ⨆ y ∈ x.leftMoves, right y + 1, x ↦ ⨅ y ∈ x.rightMoves, left y`,
is interpreted as *refining* the approximation `(left, right)` to more closely match
`(stoppingTimeRightLeft, stoppingTimeRightRight)` (which is its only fixpoint).
The induction principle says that if this refinement decreases the pair, it must be an
overestimation, and the coinduction principle says that if this refinement increases the pair,
it must be an underestimation.

-/

universe u v

/-! ### For Mathlib -/

theorem monotone_prodMk_iff {α β γ : Type*} [Preorder α] [Preorder β] [Preorder γ]
    {f : γ → α} {g : γ → β} : Monotone (fun x => (f x, g x)) ↔ Monotone f ∧ Monotone g := by
  simp_rw [Monotone, Prod.mk_le_mk, forall_and]

theorem Monotone.prodMk {α β γ : Type*} [Preorder α] [Preorder β] [Preorder γ]
    {f : γ → α} {g : γ → β} (hf : Monotone f) (hg : Monotone g) : Monotone (fun x => (f x, g x)) :=
  monotone_prodMk_iff.2 ⟨hf, hg⟩

theorem Monotone.iInf' {α β : Type*} {ι : Sort*} [Preorder α] [CompleteLattice β] {f : ι → α → β}
    (hf : ∀ (i : ι), Monotone (f i)) : Monotone (fun x => ⨅ i, f i x) :=
  (congrArg Monotone (funext (@iInf_apply _ _ _ _ _))).mp (Monotone.iInf hf)

theorem Monotone.iSup' {α β : Type*} {ι : Sort*} [Preorder α] [CompleteLattice β] {f : ι → α → β}
    (hf : ∀ (i : ι), Monotone (f i)) : Monotone (fun x => ⨆ i, f i x) :=
  (congrArg Monotone (funext (@iSup_apply _ _ _ _ _))).mp (Monotone.iSup hf)

theorem OrderHom.lfp_le_gfp {α : Type*} [CompleteLattice α] (f : α →o α) : f.lfp ≤ f.gfp :=
  f.lfp_le_fixed f.isFixedPt_gfp

instance WithTop.succAddOrder {α : Type*}
    [One α] [Add α] [PartialOrder α] [SuccAddOrder α] [NoMaxOrder α]
    [(a : α) → Decidable (Order.succ a = a)]  :
    SuccAddOrder (WithTop α) where
  succ_eq_add_one x := by
    cases x with
    | top => simp [SuccOrder.succ]
    | coe => simp [SuccOrder.succ, ← WithTop.coe_one, ← WithTop.coe_add, ← Order.succ_eq_add_one]

theorem Order.lt_add_one_iff_not_isMax {α : Type*} [Preorder α] [Add α] [One α] [SuccAddOrder α]
    (x : α) : x < x + 1 ↔ ¬IsMax x := by
  rw [← Order.succ_eq_add_one, Order.lt_succ_iff_not_isMax]

theorem Order.le_add_one {α : Type*} [Preorder α] [Add α] [One α] [SuccAddOrder α]
    (x : α) : x ≤ x + 1 := by
  rw [← Order.succ_eq_add_one]
  exact Order.le_succ x

noncomputable section
namespace LGame

/-- Refines the approximations for the left stopping times.
`stoppingTimeLeftLeft` is defined as the unique fixed point of this function. -/
private def stoppingTimeLeftApprox : (LGame.{u} → WithTop NatOrdinal.{u}) →o
    (LGame.{u} → WithTop NatOrdinal.{u}) where
  toFun f x := ⨅ y ∈ x.leftMoves, ⨆ i ∈ y.rightMoves, f i + 1
  monotone' := monotone_lam fun _ =>
    Monotone.iInf' fun _ => Monotone.iInf' fun _ => Monotone.iSup' fun i => Monotone.iSup' fun _ =>
      add_right_mono.comp (Function.monotone_eval i)

/-- Refines the approximations for the right stopping times.
`stoppingTimeRightRight` is defined as the unique fixed point of this function. -/
private def stoppingTimeRightApprox : (LGame.{u} → WithTop NatOrdinal.{u}) →o
    (LGame.{u} → WithTop NatOrdinal.{u}) where
  toFun f x := ⨅ y ∈ x.rightMoves, ⨆ i ∈ y.leftMoves, f i + 1
  monotone' := monotone_lam fun _ =>
    Monotone.iInf' fun _ => Monotone.iInf' fun _ => Monotone.iSup' fun i => Monotone.iSup' fun _ =>
      add_right_mono.comp (Function.monotone_eval i)

private theorem eq_of_finite_left {x} (hx : stoppingTimeLeftApprox x = x)
    {i : LGame.{u}} (hi : stoppingTimeLeftApprox.lfp i ≠ ⊤) :
    stoppingTimeLeftApprox.lfp i = x i := by
  have ihx : ∀ j, stoppingTimeLeftApprox.lfp j < stoppingTimeLeftApprox.lfp i →
      stoppingTimeLeftApprox.lfp j = x j := fun j hj =>
    eq_of_finite_left hx (hj.trans (lt_top_iff_ne_top.2 hi)).ne
  have hli : ¬IsMax (stoppingTimeLeftApprox.lfp i) := mt isMax_iff_eq_top.1 hi
  apply le_antisymm (stoppingTimeLeftApprox.isLeast_lfp.right hx i)
  have hg : IsGLB _ (stoppingTimeLeftApprox stoppingTimeLeftApprox.lfp i) := isGLB_biInf
  rw [stoppingTimeLeftApprox.isFixedPt_lfp] at hg
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
termination_by wellFounded_lt.wrap (stoppingTimeLeftApprox.lfp i)

private theorem eq_of_finite_right {x} (hx : stoppingTimeRightApprox x = x)
    {i : LGame.{u}} (hi : stoppingTimeRightApprox.lfp i ≠ ⊤) :
    stoppingTimeRightApprox.lfp i = x i := by
  have ihx : ∀ j, stoppingTimeRightApprox.lfp j < stoppingTimeRightApprox.lfp i →
      stoppingTimeRightApprox.lfp j = x j := fun j hj =>
    eq_of_finite_right hx (hj.trans (lt_top_iff_ne_top.2 hi)).ne
  have hli : ¬IsMax (stoppingTimeRightApprox.lfp i) := mt isMax_iff_eq_top.1 hi
  apply le_antisymm (stoppingTimeRightApprox.isLeast_lfp.right hx i)
  have hg : IsGLB _ (stoppingTimeRightApprox stoppingTimeRightApprox.lfp i) := isGLB_biInf
  rw [stoppingTimeRightApprox.isFixedPt_lfp] at hg
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
  rw [Order.lt_add_one_iff_not_isMax]
  refine mt (IsMax.mono · ?_) hli
  rw [← hu]
  exact le_iSup₂_of_le k hk (Order.le_add_one (OrderHom.lfp stoppingTimeRightApprox k))
termination_by wellFounded_lt.wrap (stoppingTimeRightApprox.lfp i)

private theorem lfp_eq_gfp_left : stoppingTimeLeftApprox.lfp = stoppingTimeLeftApprox.gfp := by
  ext i
  by_cases hi : stoppingTimeLeftApprox.lfp i = ⊤
  · exact le_antisymm (stoppingTimeLeftApprox.lfp_le_gfp i) (le_top.trans_eq hi.symm)
  · exact eq_of_finite_left stoppingTimeLeftApprox.isFixedPt_gfp hi

private theorem lfp_eq_gfp_right : stoppingTimeRightApprox.lfp = stoppingTimeRightApprox.gfp := by
  ext i
  by_cases hi : stoppingTimeRightApprox.lfp i = ⊤
  · exact le_antisymm (stoppingTimeRightApprox.lfp_le_gfp i) (le_top.trans_eq hi.symm)
  · exact eq_of_finite_right stoppingTimeRightApprox.isFixedPt_gfp hi

/-- The ordinal corresponding to the time it takes for left to force a win going first,
counted in right moves. -/
def stoppingTimeLeftLeft (x : LGame.{u}) : WithTop NatOrdinal.{u} :=
  stoppingTimeLeftApprox.lfp x

/-- The ordinal corresponding to the time it takes for right to force a win going first,
counted in left moves. -/
def stoppingTimeRightRight (x : LGame.{u}) : WithTop NatOrdinal.{u} :=
  stoppingTimeRightApprox.lfp x

/-- The ordinal corresponding to the time it takes for left to force a win going second,
counted in right moves. -/
def stoppingTimeLeftRight (x : LGame.{u}) : WithTop NatOrdinal.{u} :=
  ⨆ i ∈ x.rightMoves, stoppingTimeLeftLeft i + 1

/-- The ordinal corresponding to the time it takes for right to force a win going second,
counted in left moves. -/
def stoppingTimeRightLeft (x : LGame.{u}) : WithTop NatOrdinal.{u} :=
  ⨆ i ∈ x.leftMoves, stoppingTimeRightRight i + 1

theorem stoppingTimeLeftLeft_def (x : LGame.{u}) :
    stoppingTimeLeftLeft x = ⨅ y ∈ x.leftMoves, stoppingTimeLeftRight y :=
  congrFun stoppingTimeLeftApprox.isFixedPt_lfp.symm x

theorem stoppingTimeRightRight_def (x : LGame.{u}) :
    stoppingTimeRightRight x = ⨅ y ∈ x.rightMoves, stoppingTimeRightLeft y :=
  congrFun stoppingTimeRightApprox.isFixedPt_lfp.symm x

theorem stoppingTimeLeftRight_def (x : LGame.{u}) :
    stoppingTimeLeftRight x = ⨆ y ∈ x.rightMoves, stoppingTimeLeftLeft y + 1 :=
  rfl

theorem stoppingTimeRightLeft_def (x : LGame.{u}) :
    stoppingTimeRightLeft x = ⨆ y ∈ x.leftMoves, stoppingTimeRightRight y + 1 :=
  rfl

theorem stoppingTimeLeft_induction (left right : LGame.{u} → WithTop NatOrdinal.{u})
    (hl : ∀ x, ⨅ y ∈ x.leftMoves, right y ≤ left x)
    (hr : ∀ x, ⨆ y ∈ x.rightMoves, left y + 1 ≤ right x) :
    stoppingTimeLeftLeft ≤ left ∧ stoppingTimeLeftRight ≤ right := by
  have ul : stoppingTimeLeftApprox left ≤ left :=
    fun x ↦ (iInf₂_mono fun y _ ↦ hr y).trans (hl x)
  apply stoppingTimeLeftApprox.lfp_le at ul
  exact ⟨ul, fun x ↦ (iSup₂_mono fun y j ↦ add_right_mono (ul y)).trans (hr x)⟩

theorem stoppingTimeLeft_coinduction (left right : LGame.{u} → WithTop NatOrdinal.{u})
    (hl : ∀ x, left x ≤ ⨅ y ∈ x.leftMoves, right y)
    (hr : ∀ x, right x ≤ ⨆ y ∈ x.rightMoves, left y + 1) :
    left ≤ stoppingTimeLeftLeft ∧ right ≤ stoppingTimeLeftRight := by
  have ul : left ≤ stoppingTimeLeftApprox left :=
    fun x ↦ (hl x).trans (iInf₂_mono fun y _ ↦ hr y)
  unfold stoppingTimeLeftRight stoppingTimeLeftLeft
  simp_rw [lfp_eq_gfp_left]
  apply stoppingTimeLeftApprox.le_gfp at ul
  exact ⟨ul, fun x ↦ (hr x).trans (iSup₂_mono fun y j ↦ add_right_mono (ul y))⟩

theorem stoppingTimeRight_induction (left right : LGame.{u} → WithTop NatOrdinal.{u})
    (hl : ∀ x, ⨆ y ∈ x.leftMoves, right y + 1 ≤ left x)
    (hr : ∀ x, ⨅ y ∈ x.rightMoves, left y ≤ right x) :
    stoppingTimeRightLeft ≤ left ∧ stoppingTimeRightRight ≤ right := by
  have ur : stoppingTimeRightApprox right ≤ right :=
    fun x ↦ (iInf₂_mono fun y _ ↦ hl y).trans (hr x)
  apply stoppingTimeRightApprox.lfp_le at ur
  exact ⟨fun x ↦ (iSup₂_mono fun y j ↦ add_right_mono (ur y)).trans (hl x), ur⟩

theorem stoppingTimeRight_coinduction (left right : LGame.{u} → WithTop NatOrdinal.{u})
    (hl : ∀ x, left x ≤ ⨆ y ∈ x.leftMoves, right y + 1)
    (hr : ∀ x, right x ≤ ⨅ y ∈ x.rightMoves, left y) :
    left ≤ stoppingTimeRightLeft ∧ right ≤ stoppingTimeRightRight := by
  have ur : right ≤ stoppingTimeRightApprox right :=
    fun x ↦ (hr x).trans (iInf₂_mono fun y _ ↦ hl y)
  unfold stoppingTimeRightLeft stoppingTimeRightRight
  simp_rw [lfp_eq_gfp_right]
  apply stoppingTimeRightApprox.le_gfp at ur
  exact ⟨fun x ↦ (hl x).trans (iSup₂_mono fun y j ↦ add_right_mono (ur y)), ur⟩
