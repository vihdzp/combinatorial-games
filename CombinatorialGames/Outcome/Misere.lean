/-
Copyright (c) 2025 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/

import CombinatorialGames.Game.Birthday
import CombinatorialGames.Game.Short
import CombinatorialGames.Outcome.Defs

namespace Outcome.Misere

mutual

-- NOTE: We define these using ∀ instead of ∃ like the literature does because ∃ desugares to
-- `∃ gl, gl ∈ g.leftMoves ∧ ¬RightWinsGoingFirst gl` thus the termination check fails
-- use _def theorems instead of unfolding these

def LeftWinsGoingFirst (g : IGame) : Prop :=
  IGame.IsLeftEnd g ∨ ¬(∀ gl ∈ g.leftMoves, RightWinsGoingFirst gl)
termination_by g
decreasing_by igame_wf

def RightWinsGoingFirst (g : IGame) : Prop :=
  IGame.IsRightEnd g ∨ ¬(∀ gr ∈ g.rightMoves, LeftWinsGoingFirst gr)
termination_by g
decreasing_by igame_wf

end

theorem LeftWinsGoingFirst_def {g : IGame} :
    LeftWinsGoingFirst g
    ↔ (IGame.IsLeftEnd g ∨ (∃ gl ∈ g.leftMoves, ¬RightWinsGoingFirst gl)) := by
  constructor <;> intro h1
  · simp only [LeftWinsGoingFirst, not_forall] at h1
    apply Or.elim h1 <;> intro h2
    · exact Or.inl h2
    · exact Or.inr (bex_def.mp h2)
  · unfold LeftWinsGoingFirst
    simp only [not_forall]
    apply Or.elim h1 <;> intro h2
    · exact Or.inl h2
    · exact Or.inr (bex_def.mpr h2)

theorem RightWinsGoingFirst_def {g : IGame} :
    RightWinsGoingFirst g
    ↔ (IGame.IsRightEnd g ∨ (∃ gr ∈ g.rightMoves, ¬LeftWinsGoingFirst gr)) := by
  constructor <;> intro h1
  · simp only [RightWinsGoingFirst, not_forall] at h1
    apply Or.elim h1 <;> intro h2
    · exact Or.inl h2
    · exact Or.inr (bex_def.mp h2)
  · unfold RightWinsGoingFirst
    simp only [not_forall]
    apply Or.elim h1 <;> intro h2
    · exact Or.inl h2
    · exact Or.inr (bex_def.mpr h2)

open Classical in
/-- Game outcome if Left goes first -/
noncomputable def LeftOutcome (g : IGame) : PlayerOutcome :=
  if LeftWinsGoingFirst g then PlayerOutcome.L else PlayerOutcome.R

open Classical in
/-- Game outcome if Right goes first -/
noncomputable def RightOutcome (g : IGame) : PlayerOutcome :=
  if RightWinsGoingFirst g then PlayerOutcome.R else PlayerOutcome.L

noncomputable def MisereOutcome : IGame → Outcome :=
  fun g => PlayerOutcome.toOutcome (LeftOutcome g) (RightOutcome g)

def MisereEq (A : IGame → Prop) (g h : IGame) : Prop :=
  ∀ (x : IGame), A x → MisereOutcome (g + x) = MisereOutcome (h + x)

/-- `G =m A H` means that G =_A H -/
macro_rules | `($x =m $u $y) => `(MisereEq $u $x $y)

recommended_spelling "eq" for "=m" in [MisereEq]

theorem MisereEq_symm {A : IGame → Prop} {g h : IGame} (h1 : g =m A h) : h =m A g := by
  intro x h2
  have h3 := h1 x h2
  exact Eq.symm h3

def MisereGe (A : IGame → Prop) (g h : IGame) : Prop :=
  ∀ x, (A x → MisereOutcome (g + x) ≥ MisereOutcome (h + x))

/-- `G ≥m A H` means that G ≥_A H -/
macro_rules | `($x ≥m $u $y) => `(MisereGe $u $x $y)

recommended_spelling "ge" for "≥m" in [MisereGe]

theorem MisereGe_antisymm {A : IGame → Prop} {g h : IGame} (h1 : g ≥m A h) (h2 : h ≥m A g) :
    g =m A h := fun x h3 =>
  PartialOrder.le_antisymm (MisereOutcome (g + x)) (MisereOutcome (h + x)) (h2 x h3) (h1 x h3)

/-- No constraints (transfinite) on game form. You can prove `AnyGame x` with `trivial` -/
def AnyGame (_ : IGame) := True

class HasNeg (A : IGame → Prop) where
  has_neg (g : IGame) (h1 : A g) : A (-g)

instance : HasNeg AnyGame where
  has_neg _ _ := trivial

instance : HasNeg IGame.Short where
  has_neg g _ := IGame.Short.neg g

theorem leftEnd_leftWinsGoingFirst {g : IGame} (h1 : IGame.IsLeftEnd g) :
    LeftWinsGoingFirst g := by
  unfold LeftWinsGoingFirst
  exact Or.inl h1

theorem rightEnd_rightWinsGoingFirst {g : IGame} (h1 : IGame.IsRightEnd g) :
    RightWinsGoingFirst g := by
  unfold RightWinsGoingFirst
  exact Or.inl h1

theorem not_MisereEq_of_not_MisereGe {A : IGame → Prop} {g h : IGame} (h1 : ¬(g ≥m A h)) :
    ¬(g =m A h) := by
  simp only [MisereGe, ge_iff_le, not_forall] at h1
  obtain ⟨x, ⟨h1, h2⟩⟩ := h1
  simp only [MisereEq, not_forall]
  use x
  use h1
  exact Ne.symm (ne_of_not_le h2)

theorem not_leftWinsGoingFirst_le_P {g : IGame} (h1 : ¬LeftWinsGoingFirst g) :
    MisereOutcome g ≤ Outcome.P := by
  unfold MisereOutcome PlayerOutcome.toOutcome LeftOutcome
  cases h2 : LeftOutcome g <;> cases h3 : RightOutcome g
  all_goals simp only [h1, reduceIte, Outcome.ge_R, le_refl]

/-- `o(G) ≥ P` is equivalent to "Left can win playing second on `G`" -/
theorem not_rightWinsGoingFirst_ge_P {g : IGame} (h1 : ¬RightWinsGoingFirst g) :
    MisereOutcome g ≥ Outcome.P := by
  unfold MisereOutcome PlayerOutcome.toOutcome RightOutcome
  cases h2 : LeftOutcome g
  all_goals simp only [h1, reduceIte, ge_iff_le, le_refl, Outcome.L_ge]

theorem outcome_eq_P_leftWinsGoingFirst {g gl : IGame} (h1 : gl ∈ g.leftMoves)
    (h2 : MisereOutcome gl = Outcome.P) : LeftWinsGoingFirst g := by
  unfold MisereOutcome PlayerOutcome.toOutcome LeftOutcome RightOutcome at h2
  by_cases h3 : LeftWinsGoingFirst gl
    <;> by_cases h4 : RightWinsGoingFirst gl
    <;> simp only [h3, h4, reduceIte, reduceCtorEq] at h2
  rw [LeftWinsGoingFirst_def]
  exact Or.inr (by use gl)

theorem outcome_eq_P_rightWinsGoingFirst {g gr : IGame} (h1 : gr ∈ g.rightMoves)
    (h2 : MisereOutcome gr = Outcome.P) : RightWinsGoingFirst g := by
  unfold MisereOutcome PlayerOutcome.toOutcome LeftOutcome RightOutcome at h2
  by_cases h3 : RightWinsGoingFirst gr
    <;> by_cases h4 : LeftWinsGoingFirst gr
    <;> simp only [h3, h4, reduceIte, reduceCtorEq] at h2
  rw [RightWinsGoingFirst_def]
  exact Or.inr (by use gr)

theorem add_leftEnd_LeftWinsGoingFirst {g h : IGame} (h1 : IGame.IsLeftEnd g)
    (h2 : IGame.IsLeftEnd h) : LeftWinsGoingFirst (g + h) :=
  leftEnd_leftWinsGoingFirst (IGame.add_leftEnd_leftEnd h1 h2)

theorem add_rightEnd_RightWinsGoingFirst {g h : IGame} (h1 : IGame.IsRightEnd g)
    (h2 : IGame.IsRightEnd h) : RightWinsGoingFirst (g + h) :=
  rightEnd_rightWinsGoingFirst (IGame.add_rightEnd_rightEnd h1 h2)

theorem leftWinsGoingFirst_outcome_ge_N {g : IGame} (h1 : LeftWinsGoingFirst g) :
    MisereOutcome g ≥ Outcome.N := by
  unfold MisereOutcome PlayerOutcome.toOutcome LeftOutcome
  cases h2 : RightOutcome g
  all_goals simp only [h1, reduceIte, ge_iff_le, le_refl, Outcome.L_ge]

theorem rightWinsGoingFirst_outcome_le_N {g : IGame} (h1 : RightWinsGoingFirst g) :
    MisereOutcome g ≤ Outcome.N := by
  unfold MisereOutcome PlayerOutcome.toOutcome RightOutcome
  cases h2 : LeftOutcome g
  all_goals simp only [h1, reduceIte, le_refl, Outcome.ge_R]

theorem outcome_eq_P_not_leftWinsGoingFirst {g : IGame} (h1 : MisereOutcome g = Outcome.P) :
    ¬LeftWinsGoingFirst g := by
  intro h2
  unfold MisereOutcome PlayerOutcome.toOutcome LeftOutcome at h1
  cases h3 : RightOutcome g <;> simp only [h2, h3, reduceIte, reduceCtorEq] at h1

theorem outcome_eq_P_not_rightWinsGoingFirst {g : IGame} (h1 : MisereOutcome g = Outcome.P) :
    ¬RightWinsGoingFirst g := by
  intro h2
  unfold MisereOutcome PlayerOutcome.toOutcome RightOutcome at h1
  cases h3 : LeftOutcome g <;> simp only [h2, h3, reduceIte, reduceCtorEq] at h1

@[simp]
theorem leftOutcome_eq_R_iff_not_leftWinsFirst {g : IGame} :
    (LeftOutcome g = PlayerOutcome.R) ↔ ¬LeftWinsGoingFirst g := by
  constructor <;> intro h1
  · unfold LeftOutcome at h1
    intro h2
    simp only [h2, reduceIte, reduceCtorEq] at h1
  · unfold LeftOutcome
    simp only [h1, reduceIte]

@[simp]
theorem rightOutcome_eq_L_iff_not_rightWinsFirst {g : IGame} :
    (RightOutcome g = PlayerOutcome.L) ↔ ¬RightWinsGoingFirst g := by
  constructor <;> intro h1
  · unfold RightOutcome at h1
    intro h2
    simp only [h2, reduceIte, reduceCtorEq] at h1
  · unfold RightOutcome
    simp only [h1, reduceIte]

@[simp]
theorem neg_leftWinsFirst_iff_rightWinsFirst (g : IGame) :
    (LeftWinsGoingFirst (-g)) ↔ (RightWinsGoingFirst g) := by
  constructor <;> intro h1
  · rw [LeftWinsGoingFirst_def] at h1
    apply Or.elim h1 <;> intro h1
    · apply rightEnd_rightWinsGoingFirst
      exact IGame.leftEnd_neg_iff_rightEnd.mp h1
    · obtain ⟨gl, h1, h2⟩ := h1
      rw [RightWinsGoingFirst_def]
      apply Or.inr
      use -gl
      simp only [IGame.leftMoves_neg, Set.mem_neg] at h1
      apply And.intro h1
      exact (neg_leftWinsFirst_iff_rightWinsFirst gl).not.mpr h2
  · rw [RightWinsGoingFirst_def] at h1
    apply Or.elim h1 <;> intro h1
    · apply leftEnd_leftWinsGoingFirst
      rwa [IGame.leftEnd_neg_iff_rightEnd]
    · obtain ⟨gr, h1, h2⟩ := h1
      rw [LeftWinsGoingFirst_def]
      apply Or.inr
      use -gr
      simp only [IGame.leftMoves_neg, Set.mem_neg, neg_neg]
      apply And.intro h1
      have h3 := (neg_leftWinsFirst_iff_rightWinsFirst (-gr)).not.mp
      simp only [neg_neg] at h3
      exact h3 h2
termination_by IGame.birthday g
decreasing_by
  · simp only [IGame.leftMoves_neg, Set.mem_neg] at h1
    rw [IGame.lt_birthday_iff]
    apply Or.inr
    use -gl
    apply And.intro h1
    rw [IGame.birthday_neg]
  · rw [IGame.birthday_neg, IGame.lt_birthday_iff]
    apply Or.inr
    use gr

@[simp]
theorem neg_rightWinsFirst_iff_leftWinsFirst (g : IGame) :
    (RightWinsGoingFirst (-g)) ↔ (LeftWinsGoingFirst g) := by
  constructor <;> intro h1
  · rwa [<-neg_neg g, neg_leftWinsFirst_iff_rightWinsFirst]
  · rw [<-neg_neg g] at h1
    exact (neg_leftWinsFirst_iff_rightWinsFirst (-g)).mp h1

mutual

@[simp]
theorem leftOutcome_neg_eq_rightOutcome_conjugate (g : IGame) :
    LeftOutcome (-g) = (RightOutcome g).Conjugate := by
  unfold LeftOutcome
  rw [LeftWinsGoingFirst_def, IGame.leftMoves_neg]
  split_ifs with h1
  · apply Or.elim h1 <;> intro h1
    · have h2 : IGame.IsRightEnd g := IGame.leftEnd_neg_iff_rightEnd.mp h1
      unfold RightOutcome
      rw [RightWinsGoingFirst_def]
      simp only [h2, true_or, reduceIte]
      rfl
    · obtain ⟨gl, h1, h2⟩ := h1
      unfold RightOutcome
      have h3 : RightWinsGoingFirst g := by
        rw [RightWinsGoingFirst_def]
        apply Or.inr
        use -gl
        apply And.intro h1
        rw [<-rightOutcome_eq_L_iff_not_rightWinsFirst] at h2
        rw [<-leftOutcome_eq_R_iff_not_leftWinsFirst]
        apply Eq.symm
        have h3 : PlayerOutcome.R.Conjugate = PlayerOutcome.L  := rfl
        rw [<-PlayerOutcome.eq_iff_conjugate_eq, h3, <-h2]
        have h4 := rightOutcome_neg_eq_leftOutcome_conjugate (-gl)
        rwa [neg_neg] at h4
      simp only [h3, reduceIte]
      rfl
  · simp only [Set.mem_neg, not_or, not_exists, not_and, not_not] at h1
    obtain ⟨h1, h2⟩ := h1
    unfold RightOutcome
    have h3 : ¬RightWinsGoingFirst g := by
      unfold RightWinsGoingFirst
      simp only [not_forall, not_or, not_exists, not_not]
      have h3 : ¬IGame.IsRightEnd g := by
        intro h3
        unfold IGame.IsLeftEnd at h1
        simp only [IGame.leftMoves_neg, Set.neg_eq_empty] at h1
        exact h1 h3
      apply And.intro h3
      intro gl h4
      have h5 := h2 (-gl)
      rw [neg_neg] at h5
      have h6 := h5 h4
      rw [RightWinsGoingFirst_def] at h6
      apply Or.elim h6 <;> intro h6
      · rw [LeftWinsGoingFirst_def]
        apply Or.inl
        unfold IGame.IsRightEnd at h6
        simp only [IGame.rightMoves_neg, Set.neg_eq_empty] at h6
        exact h6
      · obtain ⟨x, h6, h7⟩ := h6
        simp only [IGame.rightMoves_neg, Set.mem_neg] at h6
        rw [LeftWinsGoingFirst_def]
        apply Or.inr
        use -x
        apply And.intro h6
        have h8 : ¬LeftWinsGoingFirst (- (-x)) := by
          simp only [neg_neg]
          exact h7
        exact (neg_leftWinsFirst_iff_rightWinsFirst (-x)).not.mp h8
    simp only [h3, reduceIte]
    rfl
termination_by g
decreasing_by igame_wf

@[simp]
theorem rightOutcome_neg_eq_leftOutcome_conjugate (g : IGame) :
    RightOutcome (-g) = (LeftOutcome g).Conjugate := by
  unfold RightOutcome
  rw [RightWinsGoingFirst_def, IGame.rightMoves_neg]
  split_ifs with h1
  · apply Or.elim h1 <;> intro h1
    · have h2 : IGame.IsLeftEnd g := IGame.rightEnd_neg_iff_leftEnd.mp h1
      unfold LeftOutcome
      rw [LeftWinsGoingFirst_def]
      simp only [h2, true_or, reduceIte]
      rfl
    · obtain ⟨gr, h1, h2⟩ := h1
      unfold LeftOutcome
      have h3 : LeftWinsGoingFirst g := by
        rw [LeftWinsGoingFirst_def]
        apply Or.inr
        use -gr
        apply And.intro h1
        rw [<-leftOutcome_eq_R_iff_not_leftWinsFirst] at h2
        rw [<-rightOutcome_eq_L_iff_not_rightWinsFirst]
        apply Eq.symm
        have h3 : PlayerOutcome.L.Conjugate = PlayerOutcome.R  := rfl
        rw [<-PlayerOutcome.eq_iff_conjugate_eq, h3, <-h2]
        have h4 := leftOutcome_neg_eq_rightOutcome_conjugate (-gr)
        rwa [neg_neg] at h4
      simp only [h3, reduceIte]
      rfl
  · simp only [Set.mem_neg, not_or, not_exists, not_and, not_not] at h1
    obtain ⟨h1, h2⟩ := h1
    unfold LeftOutcome
    have h3 : ¬LeftWinsGoingFirst g := by
      unfold LeftWinsGoingFirst
      simp only [not_forall, not_or, not_exists, not_not]
      have h3 : ¬IGame.IsLeftEnd g := by
        intro h3
        unfold IGame.IsRightEnd at h1
        simp only [IGame.rightMoves_neg, Set.neg_eq_empty] at h1
        exact h1 h3
      apply And.intro h3
      intro gl h4
      have h5 := h2 (-gl)
      rw [neg_neg] at h5
      have h6 := h5 h4
      rw [LeftWinsGoingFirst_def] at h6
      apply Or.elim h6 <;> intro h6
      · rw [RightWinsGoingFirst_def]
        apply Or.inl
        unfold IGame.IsLeftEnd at h6
        simp only [IGame.leftMoves_neg, Set.neg_eq_empty] at h6
        exact h6
      · obtain ⟨x, h6, h7⟩ := h6
        simp only [IGame.leftMoves_neg, Set.mem_neg] at h6
        rw [RightWinsGoingFirst_def]
        apply Or.inr
        use -x
        apply And.intro h6
        exact (neg_leftWinsFirst_iff_rightWinsFirst x).not.mpr h7
    simp only [h3, reduceIte]
    rfl
termination_by g
decreasing_by igame_wf

end

@[simp]
theorem conjugate_of_conjugates {g : IGame} :
    PlayerOutcome.toOutcome (RightOutcome g).Conjugate (LeftOutcome g).Conjugate
    = (MisereOutcome g).Conjugate := by
  cases h1 : RightOutcome g <;> cases h2 : LeftOutcome g
  all_goals simp only [h1, h2, PlayerOutcome.toOutcome, PlayerOutcome.Conjugate,
                       Outcome.Conjugate, MisereOutcome]

@[simp]
theorem outcome_conjugate_eq_outcome_neg {g : IGame} :
    (MisereOutcome g).Conjugate = MisereOutcome (-g) := by
  unfold Outcome.Conjugate
  cases h1 : MisereOutcome g
  all_goals
  · unfold MisereOutcome
    rw [rightOutcome_neg_eq_leftOutcome_conjugate, leftOutcome_neg_eq_rightOutcome_conjugate,
        conjugate_of_conjugates, h1]
    rfl

private theorem HasNeg.not_ge_neg_iff.aux {A : IGame → Prop} [HasNeg A] {g h : IGame} (h1 : g ≥m A h) :
    (-h) ≥m A (-g) := by
  unfold MisereGe at *
  intro x h0
  have h2 := h1 (-x)
  have h3 := Outcome.outcome_ge_conjugate_le (h2 (HasNeg.has_neg x h0))
  have h4 : MisereOutcome (-h + x) = (MisereOutcome (-h + x)).Conjugate.Conjugate :=
    Eq.symm Outcome.conjugate_conjugate_eq_self
  have h5 : (MisereOutcome (-h + x)).Conjugate.Conjugate = (MisereOutcome (h + (-x))).Conjugate :=
    by rw [outcome_conjugate_eq_outcome_neg, neg_add_rev, neg_neg, add_comm]
  rw [h4, h5]
  have h6 : (MisereOutcome (g + (-x))).Conjugate = MisereOutcome (-g + x) :=
    by rw [outcome_conjugate_eq_outcome_neg, neg_add_rev, neg_neg, add_comm]
  rw [<-h6]
  apply Outcome.outcome_ge_conjugate_le
  exact h2 (HasNeg.has_neg x h0)

@[simp]
theorem HasNeg.neg_ge_neg_iff {A : IGame → Prop} [HasNeg A] {g h : IGame} :
    (-h) ≥m A (-g) ↔ g ≥m A h := by
  constructor <;> intro h1
  · have h2 := not_ge_neg_iff.aux h1
    simp only [neg_neg] at h2
    exact h2
  · exact not_ge_neg_iff.aux h1

private theorem proposition6_1 (g h : IGame) :
    (g ≥m AnyGame h)
    ↔ (∀ (x : IGame),
      (MisereOutcome (h + x) ≥ Outcome.P → MisereOutcome (g + x) ≥ Outcome.P)
      ∧ (MisereOutcome (h + x) ≥ Outcome.N → MisereOutcome (g + x) ≥ Outcome.N)) := by
  constructor <;> intro h1
  · -- => is immediate
    intro x
    unfold MisereGe at h1
    constructor <;> intro h2
    · exact Preorder.le_trans _ (MisereOutcome (h + x)) (MisereOutcome (g + x)) h2 (h1 x trivial)
    · exact Preorder.le_trans _ (MisereOutcome (h + x)) (MisereOutcome (g + x)) h2 (h1 x trivial)
  · -- For the converse, we must show that o(G + X) > o(H + X), for all X.
    unfold MisereGe
    intro x _
    obtain ⟨h2, h3⟩ := h1 x
    cases ho : MisereOutcome (h + x) with
    | R =>
      -- If o(H + X) = R, then there is nothing to prove
      exact Outcome.ge_R (MisereOutcome (g + x))
    | N =>
      -- If o(H + X) = P or N, it is immediate from (i) or (ii)
      rw [ho] at h3
      exact h3 (Preorder.le_refl Outcome.N)
    | P =>
      rw [ho] at h2
      exact h2 (Preorder.le_refl Outcome.P)
    | L =>
      -- Finally, if o(H + X) = L, then by (i) and (ii) we have o(G + X) > both P and N,
      -- whence o(G + X) = L.
      rw [ho] at h2 h3
      have h4 := h2 (Outcome.L_ge Outcome.P)
      have h5 := h3 (Outcome.L_ge Outcome.N)
      have h6 := Outcome.ge_P_ge_N_eq_L h4 h5
      exact le_of_eq (Eq.symm h6)

end Outcome.Misere
