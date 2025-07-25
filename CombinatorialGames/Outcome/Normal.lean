import CombinatorialGames.Outcome.Defs
import CombinatorialGames.Game.IGame

mutual

def LeftWinsGoingFirst (g : IGame) : Prop := ¬(∀ gl ∈ g.leftMoves, RightWinsGoingFirst gl)
termination_by g
decreasing_by igame_wf

def RightWinsGoingFirst (g : IGame) : Prop := ¬(∀ gr ∈ g.rightMoves, LeftWinsGoingFirst gr)
termination_by g
decreasing_by igame_wf

end

theorem LeftWinsGoingFirst_def {g : IGame} :
    LeftWinsGoingFirst g ↔ (∃ gl ∈ g.leftMoves, ¬RightWinsGoingFirst gl) := by
  constructor <;> intro h1
  · simp only [LeftWinsGoingFirst, not_forall] at h1
    obtain ⟨gl, h1, h2⟩ := h1
    use gl
  · obtain ⟨gl, h1, h2⟩ := h1
    simp only [LeftWinsGoingFirst, not_forall]
    use gl

theorem RightWinsGoingFirst_def {g : IGame} :
    RightWinsGoingFirst g ↔ (∃ gr ∈ g.rightMoves, ¬LeftWinsGoingFirst gr) := by
  constructor <;> intro h1
  · simp only [RightWinsGoingFirst, not_forall] at h1
    obtain ⟨gr, h1, h2⟩ := h1
    use gr
  · obtain ⟨gr, h1, h2⟩ := h1
    simp only [RightWinsGoingFirst, not_forall]
    use gr

open Classical in
/-- Game outcome if Left goes first -/
noncomputable def LeftOutcome (g : IGame) : PlayerOutcome :=
  if LeftWinsGoingFirst g then PlayerOutcome.L else PlayerOutcome.R

open Classical in
/-- Game outcome if Right goes first -/
noncomputable def RightOutcome (g : IGame) : PlayerOutcome :=
  if RightWinsGoingFirst g then PlayerOutcome.R else PlayerOutcome.L

noncomputable def NormalOutcome : IGame → Outcome :=
  fun g => PlayerOutcomesToGameOutcome (LeftOutcome g) (RightOutcome g)

theorem eq_zero_outcome_P (g : IGame) (h1 : g = 0) : NormalOutcome g = Outcome.P := by
  rw [h1]
  unfold NormalOutcome LeftOutcome RightOutcome
  rw [LeftWinsGoingFirst_def, RightWinsGoingFirst_def]
  simp only [IGame.leftMoves_zero, Set.mem_empty_iff_false, false_and, exists_const, reduceIte,
             IGame.rightMoves_zero]
  rfl
