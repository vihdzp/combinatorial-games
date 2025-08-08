import CombinatorialGames.Game.Loopy.IGame

namespace LGame

/-- A surviving strategy for Left, going second.

This is a set of states, such that for every move Right makes, Left can bring it back
to the set. -/
def LeftStrategy (s : Set LGame) : Prop :=
  ∀ y ∈ s, ∀ z ∈ y.rightMoves, ∃ r ∈ z.leftMoves, r ∈ s

/-- A surviving strategy for Right, going second.

This is a set of states, such that for every move Left makes, Right can bring it back
to the set. -/
def RightStrategy (s : Set LGame) : Prop :=
  ∀ y ∈ s, ∀ z ∈ y.leftMoves, ∃ r ∈ z.rightMoves, r ∈ s

@[simp]
theorem leftStrategy_neg {s : Set LGame} : LeftStrategy (-s) ↔ RightStrategy s := by
  simp [LeftStrategy, RightStrategy]

@[simp]
theorem rightStrategy_neg {s : Set LGame} : RightStrategy (-s) ↔ LeftStrategy s := by
  simp_rw [← leftStrategy_neg, neg_neg]

/-- `IsLeftSurviving x` means that left survives `x` going second. -/
def IsLeftSurviving (x : LGame) : Prop := ∃ s : Set LGame, x ∈ s ∧ LeftStrategy s

/-- `IsRightSurviving x` means that right survives `x` going second. -/
def IsRightSurviving (x : LGame) : Prop := ∃ s : Set LGame, x ∈ s ∧ RightStrategy s

theorem leftStrategy_iUnion {ι} {s : ι → Set LGame} (h : ∀ i, LeftStrategy (s i)) :
    LeftStrategy (⋃ i, s i) :=
  fun y hy z hz ↦ have ⟨i, hi⟩ := Set.mem_iUnion.mp hy
    have ⟨r, hrz, hr⟩ := h i y hi z hz
    ⟨r, hrz, Set.mem_iUnion_of_mem i hr⟩

theorem rightStrategy_iUnion {ι} {s : ι → Set LGame} (h : ∀ i, RightStrategy (s i)) :
    RightStrategy (⋃ i, s i) :=
  fun y hy z hz ↦ have ⟨i, hi⟩ := Set.mem_iUnion.mp hy
    have ⟨r, hrz, hr⟩ := h i y hi z hz
    ⟨r, hrz, Set.mem_iUnion_of_mem i hr⟩

mutual
  /-- `IsLeftWinning x` means that left wins `x` going second. -/
  inductive IsLeftWinning : LGame → Prop where
    | intro (x : LGame) : (∀ y ∈ x.rightMoves, IsRightLosing y) → IsLeftWinning x
  /-- `IsRightLosing x` means that right loses `x` going second. -/
  inductive IsRightLosing : LGame → Prop where
    | intro (x y : LGame) : y ∈ x.leftMoves → IsLeftWinning y → IsRightLosing x
end

mutual
  /-- `IsRightWinning x` means that right wins `x` going second. -/
  inductive IsRightWinning : LGame → Prop where
    | intro (x : LGame) : (∀ y ∈ x.leftMoves, IsLeftLosing y) → IsRightWinning x
  /-- `IsLeftLosing x` means that left loses `x` going second. -/
  inductive IsLeftLosing : LGame → Prop where
    | intro (x y : LGame) : y ∈ x.rightMoves → IsRightWinning y → IsLeftLosing x
end

theorem isLeftWinning_iff_forall {x : LGame} :
    IsLeftWinning x ↔ ∀ y ∈ x.rightMoves, IsRightLosing y where
  mp h := h.rec (motive_2 := fun _ _ ↦ True) (fun _ h _ ↦ h) fun _ _ _ _ _ ↦ trivial
  mpr := .intro x

theorem isRightWinning_iff_forall {x : LGame} :
    IsRightWinning x ↔ ∀ y ∈ x.leftMoves, IsLeftLosing y where
  mp h := h.rec (motive_2 := fun _ _ ↦ True) (fun _ h _ ↦ h) fun _ _ _ _ _ ↦ trivial
  mpr := .intro x

theorem isRightLosing_iff_exists {x : LGame} :
    IsRightLosing x ↔ ∃ y ∈ x.leftMoves, IsLeftWinning y where
  mp h := h.rec (motive_1 := fun _ _ ↦ True) (fun _ _ _ ↦ trivial) fun _x y hyx hy _ ↦ ⟨y, hyx, hy⟩
  mpr := fun ⟨y, hyx, hy⟩ ↦ .intro x y hyx hy

theorem isLeftLosing_iff_exists {x : LGame} :
    IsLeftLosing x ↔ ∃ y ∈ x.rightMoves, IsRightWinning y where
  mp h := h.rec (motive_1 := fun _ _ ↦ True) (fun _ _ _ ↦ trivial) fun _x y hyx hy _ ↦ ⟨y, hyx, hy⟩
  mpr := fun ⟨y, hyx, hy⟩ ↦ .intro x y hyx hy

theorem leftStrategy_isLeftWinning : LeftStrategy {x | IsLeftWinning x} :=
  fun _ ↦ (isLeftWinning_iff_forall.trans (by simp [isRightLosing_iff_exists])).mp

theorem rightStrategy_isRightWinning : RightStrategy {x | IsRightWinning x} :=
  fun _ ↦ (isRightWinning_iff_forall.trans (by simp [isLeftLosing_iff_exists])).mp

theorem IsLeftWinning.isLeftSurviving {x : LGame} (h : IsLeftWinning x) : IsLeftSurviving x :=
  ⟨_, h, leftStrategy_isLeftWinning⟩

theorem IsRightWinning.isRightSurviving {x : LGame} (h : IsRightWinning x) : IsRightSurviving x :=
  ⟨_, h, rightStrategy_isRightWinning⟩

theorem leftStrategy_not_isLeftLosing : LeftStrategy {x | ¬ IsLeftLosing x} :=
  fun x hx y hy ↦ by
    simp_rw [Set.mem_setOf, isLeftLosing_iff_exists, isRightWinning_iff_forall] at hx
    push_neg at hx
    exact hx y hy

theorem rightStrategy_not_isRightLosing : RightStrategy {x | ¬ IsRightLosing x} :=
  fun x hx y hy ↦ by
    simp_rw [Set.mem_setOf, isRightLosing_iff_exists, isLeftWinning_iff_forall] at hx
    push_neg at hx
    exact hx y hy

theorem isLeftSurviving_iff_not_isLeftLosing {x : LGame} :
    IsLeftSurviving x ↔ ¬ IsLeftLosing x where
  mp ls ll := ll.rec (motive_1 := fun _ _ ↦ _) (fun _ _ ↦ id)
    (fun x y hyx _ hy ⟨s, hx, hs⟩ ↦ have ⟨r, hr⟩ := hs x hx y hyx; hy r hr.1 ⟨s, hr.2, hs⟩) ls
  mpr h := ⟨_, h, leftStrategy_not_isLeftLosing⟩

theorem isRightSurviving_iff_not_isRightLosing {x : LGame} :
    IsRightSurviving x ↔ ¬ IsRightLosing x where
  mp rs rl := rl.rec (motive_1 := fun _ _ ↦ _) (fun _ _ ↦ id)
    (fun x y hyx _ hy ⟨s, hx, hs⟩ ↦ have ⟨r, hr⟩ := hs x hx y hyx; hy r hr.1 ⟨s, hr.2, hs⟩) rs
  mpr h := ⟨_, h, rightStrategy_not_isRightLosing⟩

theorem isLeftSurviving_iff_forall {x : LGame} :
    IsLeftSurviving x ↔ ∀ y ∈ x.rightMoves, ¬ IsRightWinning y := by
  rw [isLeftSurviving_iff_not_isLeftLosing, isLeftLosing_iff_exists]; push_neg; rfl

theorem isRightSurviving_iff_forall {x : LGame} :
    IsRightSurviving x ↔ ∀ y ∈ x.leftMoves, ¬ IsLeftWinning y := by
  rw [isRightSurviving_iff_not_isRightLosing, isRightLosing_iff_exists]; push_neg; rfl

theorem not_isLeftWinning_iff_exists {x : LGame} :
    ¬ IsLeftWinning x ↔ ∃ y ∈ x.rightMoves, IsRightSurviving y := by
  simp [isLeftWinning_iff_forall, isRightSurviving_iff_not_isRightLosing]

theorem not_isRightWinning_iff_exists {x : LGame} :
    ¬ IsRightWinning x ↔ ∃ y ∈ x.leftMoves, IsLeftSurviving y := by
  simp [isRightWinning_iff_forall, isLeftSurviving_iff_not_isLeftLosing]

/-- `IsLeftDrawing x` means that left draws `x` going second. -/
def IsLeftDrawing (x : LGame) : Prop := IsLeftSurviving x ∧ ¬ IsLeftWinning x

/-- `IsRightDrawing x` means that right draws `x` going second. -/
def IsRightDrawing (x : LGame) : Prop := IsRightSurviving x ∧ ¬ IsRightWinning x

/-- The three possible outcomes of a game. -/
inductive Outcome : Type | win | draw | loss

/-- `leftOutcome x` is the outcome of `x` with left going second. -/
noncomputable def leftOutcome (x : LGame) : Outcome := by classical
  exact if IsLeftSurviving x then if IsLeftWinning x then .win else .draw else .loss

/-- `rightOutcome x` is the outcome of `x` with right going second. -/
noncomputable def rightOutcome (x : LGame) : Outcome := by classical
  exact if IsRightSurviving x then if IsRightWinning x then .win else .draw else .loss

theorem leftOutcome_eq_loss_iff {x : LGame} : leftOutcome x = .loss ↔ IsLeftLosing x := by
  classical rw [leftOutcome, Ne.ite_eq_right_iff, isLeftSurviving_iff_not_isLeftLosing, not_not]
  split_ifs <;> rintro ⟨_⟩

theorem rightOutcome_eq_loss_iff {x : LGame} : rightOutcome x = .loss ↔ IsRightLosing x := by
  classical rw [rightOutcome, Ne.ite_eq_right_iff, isRightSurviving_iff_not_isRightLosing, not_not]
  split_ifs <;> rintro ⟨_⟩

theorem leftOutcome_eq_draw_iff {x : LGame} : leftOutcome x = .draw ↔ IsLeftDrawing x := by
  classical rw [leftOutcome]
  split_ifs with s w
  on_goal 2 => simpa using ⟨s, w⟩
  all_goals rw [false_iff, IsLeftDrawing, not_and_or, not_not]
  exacts [.inr w, .inl s]

theorem rightOutcome_eq_draw_iff {x : LGame} : rightOutcome x = .draw ↔ IsRightDrawing x := by
  classical rw [rightOutcome]
  split_ifs with s w
  on_goal 2 => simpa using ⟨s, w⟩
  all_goals rw [false_iff, IsRightDrawing, not_and_or, not_not]
  exacts [.inr w, .inl s]

theorem leftOutcome_eq_win_iff {x : LGame} : leftOutcome x = .win ↔ IsLeftWinning x := by
  classical rw [leftOutcome]
  split_ifs with s w
  on_goal 3 => exact false_iff _ ▸ mt (·.isLeftSurviving) s
  all_goals simpa using w

theorem rightOutcome_eq_win_iff {x : LGame} : rightOutcome x = .win ↔ IsRightWinning x := by
  classical rw [rightOutcome]
  split_ifs with s w
  on_goal 3 => exact false_iff _ ▸ mt (·.isRightSurviving) s
  all_goals simpa using w

theorem leftOutcome_trichotomy (x : LGame) :
    IsLeftWinning x ∨ IsLeftDrawing x ∨ IsLeftLosing x := by
  rw [← leftOutcome_eq_win_iff, ← leftOutcome_eq_draw_iff, ← leftOutcome_eq_loss_iff]
  cases x.leftOutcome <;> simp

theorem rightOutcome_trichotomy (x : LGame) :
    IsRightWinning x ∨ IsRightDrawing x ∨ IsRightLosing x := by
  rw [← rightOutcome_eq_win_iff, ← rightOutcome_eq_draw_iff, ← rightOutcome_eq_loss_iff]
  cases x.rightOutcome <;> simp

theorem isSurviving_total_left (x : LGame) :
    (∃ y ∈ x.leftMoves, IsLeftSurviving y) ∨ IsRightSurviving x := by
  rw [← not_isRightWinning_iff_exists, ← imp_iff_not_or]; exact (·.isRightSurviving)

theorem isSurviving_total_right (x : LGame) :
    IsLeftSurviving x ∨ (∃ y ∈ x.rightMoves, IsRightSurviving y) := by
  rw [← not_isLeftWinning_iff_exists, ← imp_iff_or_not]; exact (·.isLeftSurviving)

/-- If there is no infinite play starting from `x` with left going second,
then `x` cannot end in a draw with left going second. -/
-- Note: the spelling `Relation.Comp (· ∈ ·.leftMoves) (· ∈ ·.rightMoves)` is slightly longer
theorem not_isLeftDrawing_of_acc_comp {x : LGame}
    (h : Acc (fun z x ↦ ∃ y ∈ x.rightMoves, z ∈ y.leftMoves) x) : ¬ IsLeftDrawing x :=
  h.rec fun _x _ ih ⟨s, nl⟩ ↦
    have ⟨y, hyx, hy⟩ := not_isLeftWinning_iff_exists.mp nl
    have ⟨z, hzy, hz⟩ := not_isRightWinning_iff_exists.mp (isLeftSurviving_iff_forall.mp s y hyx)
    ih z ⟨y, hyx, hzy⟩ ⟨hz, isRightSurviving_iff_forall.mp hy z hzy⟩

/-- If there is no infinite play starting by from `x` with right going second,
then `x` cannot end in a draw with right going second. -/
theorem not_isRightDrawing_of_acc_comp {x : LGame}
    (h : Acc (fun z x ↦ ∃ y ∈ x.leftMoves, z ∈ y.rightMoves) x) : ¬ IsRightDrawing x :=
  h.rec fun _x _ ih ⟨s, nl⟩ ↦
    have ⟨y, hyx, hy⟩ := not_isRightWinning_iff_exists.mp nl
    have ⟨z, hzy, hz⟩ := not_isLeftWinning_iff_exists.mp (isRightSurviving_iff_forall.mp s y hyx)
    ih z ⟨y, hyx, hzy⟩ ⟨hz, isLeftSurviving_iff_forall.mp hy z hzy⟩

theorem not_isLeftDrawing_of_acc_isOption {x : LGame} (h : Acc IsOption x) : ¬ IsLeftDrawing x :=
  not_isLeftDrawing_of_acc_comp <| Subrelation.accessible
    (fun ⟨_, hyx, hzy⟩ ↦ .tail (.single <| .inl hzy) (.inr hyx)) h.transGen

theorem not_isRightDrawing_of_acc_isOption {x : LGame} (h : Acc IsOption x) : ¬ IsRightDrawing x :=
  not_isRightDrawing_of_acc_comp <| Subrelation.accessible
    (fun ⟨_, hyx, hzy⟩ ↦ .tail (.single <| .inr hzy) (.inl hyx)) h.transGen

end LGame

theorem IGame.not_isLeftDrawing (x : IGame) : ¬ x.toLGame.IsLeftDrawing :=
  LGame.not_isLeftDrawing_of_acc_isOption x.acc_toLGame

theorem IGame.not_isRightDrawing (x : IGame) : ¬ x.toLGame.IsRightDrawing :=
  LGame.not_isRightDrawing_of_acc_isOption x.acc_toLGame
