import CombinatorialGames.Game.Loopy.Basic
import CombinatorialGames.Game.IGame

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

theorem isLeftSurviving_iff_forall_exists {x : LGame} :
    IsLeftSurviving x ↔ ∀ y ∈ x.rightMoves, ∃ r ∈ y.leftMoves, IsLeftSurviving r where
  mp h y hyx := have ⟨str, hx, hstr⟩ := h
    have ⟨r, hry, hr⟩ := hstr x hx y hyx
    ⟨r, hry, str, hr, hstr⟩
  mpr h := by
    choose r hr str mem hstr using h
    let s (y : {y // y ∈ x.rightMoves}) := str y y.2
    refine ⟨insert x (⋃ y, s y), .inl rfl, fun y hy z hz ↦ ?_⟩
    obtain rfl | hy := hy
    · exact ⟨_, hr .., .inr (Set.mem_iUnion_of_mem ⟨z, hz⟩ (mem ..))⟩
    have ⟨r, hrz, hr⟩ := leftStrategy_iUnion (s := s) (fun y ↦ hstr y y.2) y hy z hz
    exact ⟨r, hrz, .inr hr⟩

theorem isRightSurviving_iff_forall_exists {x : LGame} :
    IsRightSurviving x ↔ ∀ y ∈ x.leftMoves, ∃ r ∈ y.rightMoves, IsRightSurviving r where
  mp h y hyx := have ⟨str, hx, hstr⟩ := h
    have ⟨r, hry, hr⟩ := hstr x hx y hyx
    ⟨r, hry, str, hr, hstr⟩
  mpr h := by
    choose r hr str mem hstr using h
    let s (y : {y // y ∈ x.leftMoves}) := str y y.2
    refine ⟨insert x (⋃ y, s y), .inl rfl, fun y hy z hz ↦ ?_⟩
    obtain rfl | hy := hy
    · exact ⟨_, hr .., .inr (Set.mem_iUnion_of_mem ⟨z, hz⟩ (mem ..))⟩
    have ⟨r, hrz, hr⟩ := rightStrategy_iUnion (s := s) (fun y ↦ hstr y y.2) y hy z hz
    exact ⟨r, hrz, .inr hr⟩

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
  mp h := h.rec (motive_1 := fun _ _ ↦ True) (fun _ _ _ ↦ trivial) fun x y hyx hy _ ↦ ⟨y, hyx, hy⟩
  mpr := fun ⟨y, hyx, hy⟩ ↦ .intro x y hyx hy

theorem isLeftLosing_iff_exists {x : LGame} :
    IsLeftLosing x ↔ ∃ y ∈ x.rightMoves, IsRightWinning y where
  mp h := h.rec (motive_1 := fun _ _ ↦ True) (fun _ _ _ ↦ trivial) fun x y hyx hy _ ↦ ⟨y, hyx, hy⟩
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

theorem isLeftSuriving_iff_not_isLeftLosing {x : LGame} : IsLeftSurviving x ↔ ¬ IsLeftLosing x where
  mp ls ll := ll.rec (motive_1 := fun _ _ ↦ _) (fun _ _ ↦ id)
    (fun x y hyx _ hy ⟨s, hx, hs⟩ ↦ have ⟨r, hr⟩ := hs x hx y hyx; hy r hr.1 ⟨s, hr.2, hs⟩) ls
  mpr h := ⟨_, h, leftStrategy_not_isLeftLosing⟩

theorem isRightSuriving_iff_not_isRightLosing {x : LGame} :
    IsRightSurviving x ↔ ¬ IsRightLosing x where
  mp rs rl := rl.rec (motive_1 := fun _ _ ↦ _) (fun _ _ ↦ id)
    (fun x y hyx _ hy ⟨s, hx, hs⟩ ↦ have ⟨r, hr⟩ := hs x hx y hyx; hy r hr.1 ⟨s, hr.2, hs⟩) rs
  mpr h := ⟨_, h, rightStrategy_not_isRightLosing⟩

theorem isLeftSurviving_iff_forall {x : LGame} :
    IsLeftSurviving x ↔ ∀ y ∈ x.rightMoves, ¬ IsRightWinning y := by
  rw [isLeftSuriving_iff_not_isLeftLosing, isLeftLosing_iff_exists]; push_neg; rfl

theorem isRightSurviving_iff_forall {x : LGame} :
    IsRightSurviving x ↔ ∀ y ∈ x.leftMoves, ¬ IsLeftWinning y := by
  rw [isRightSuriving_iff_not_isRightLosing, isRightLosing_iff_exists]; push_neg; rfl

theorem left_or_right_survive_left (x : LGame) :
    (∃ y ∈ x.leftMoves, IsLeftSurviving y) ∨ IsRightSurviving x := by
  rw [or_iff_not_imp_left, isRightSurviving_iff_forall]
  push_neg
  exact forall₂_imp fun _ _ ↦ mt (·.isLeftSurviving)

end LGame
