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

/-- `IsLeftWinning x` means that left wins `x` going second. -/
inductive IsLeftWinning : LGame → Prop where
  | intro' (x : LGame) (f : ∀ y ∈ x.rightMoves, LGame) :
      (∀ y (hy : y ∈ x.rightMoves), f y hy ∈ y.leftMoves) →
      (∀ y (hy : y ∈ x.rightMoves), IsLeftWinning (f y hy)) → IsLeftWinning x

/-- `IsRightWinning x` means that right wins `x` going second. -/
inductive IsRightWinning : LGame → Prop where
  | intro' (x : LGame) (f : ∀ y ∈ x.leftMoves, LGame) :
      (∀ y (hy : y ∈ x.leftMoves), f y hy ∈ y.rightMoves) →
      (∀ y (hy : y ∈ x.leftMoves), IsRightWinning (f y hy)) → IsRightWinning x

/-- `IsLeftLosing x` means that left loses `x` going second. -/
def IsLeftLosing (x : LGame) : Prop := ∃ y ∈ x.rightMoves, IsRightWinning y

/-- `IsRightLosing x` means that right loses `x` going second. -/
def IsRightLosing (x : LGame) : Prop := ∃ y ∈ x.leftMoves, IsLeftWinning y

theorem IsLeftWinning.intro (x : LGame)
    (h : ∀ y ∈ x.rightMoves, ∃ z ∈ y.leftMoves, IsLeftWinning z) :
    IsLeftWinning x := by
  choose f hf using h
  exact .intro' x f (hf · · |>.1) (hf · · |>.2)

theorem IsRightWinning.intro (x : LGame)
    (h : ∀ y ∈ x.leftMoves, ∃ z ∈ y.rightMoves, IsRightWinning z) :
    IsRightWinning x := by
  choose f hf using h
  exact .intro' x f (hf · · |>.1) (hf · · |>.2)

theorem isLeftWinning_iff_forall {x : LGame} :
    IsLeftWinning x ↔ ∀ y ∈ x.rightMoves, IsRightLosing y where
  mp := by rintro ⟨_, f, h1, h2⟩ y hy; exact ⟨_, h1 y hy, h2 y hy⟩
  mpr := .intro x

theorem isRightWinning_iff_forall {x : LGame} :
    IsRightWinning x ↔ ∀ y ∈ x.leftMoves, IsLeftLosing y where
  mp := by rintro ⟨_, f, h1, h2⟩ y hy; exact ⟨_, h1 y hy, h2 y hy⟩
  mpr := .intro x

theorem leftStrategy_isLeftWinning : LeftStrategy {x | IsLeftWinning x} :=
  fun _ ↦ isLeftWinning_iff_forall.mp

theorem rightStrategy_isRightWinning : RightStrategy {x | IsRightWinning x} :=
  fun _ ↦ isRightWinning_iff_forall.mp

theorem IsLeftWinning.isLeftSurviving {x : LGame} (h : IsLeftWinning x) : IsLeftSurviving x :=
  ⟨_, h, leftStrategy_isLeftWinning⟩

theorem IsRightWinning.isRightSurviving {x : LGame} (h : IsRightWinning x) : IsRightSurviving x :=
  ⟨_, h, rightStrategy_isRightWinning⟩

theorem leftStrategy_not_isLeftLosing : LeftStrategy {x | ¬ IsLeftLosing x} :=
  fun x hx y hy ↦ by
    simp_rw [Set.mem_setOf, IsLeftLosing, isRightWinning_iff_forall] at hx
    push_neg at hx
    exact hx y hy

theorem rightStrategy_not_isRightLosing : RightStrategy {x | ¬ IsRightLosing x} :=
  fun x hx y hy ↦ by
    simp_rw [Set.mem_setOf, IsRightLosing, isLeftWinning_iff_forall] at hx
    push_neg at hx
    exact hx y hy

private theorem IsRightWinning.not_isLeftSurviving {x : LGame} (h : IsRightWinning x) :
    ∀ y ∈ x.leftMoves, ¬ IsLeftSurviving y :=
  h.rec fun _x _f hf _ ih y hyx ⟨str, hy, hstr⟩ ↦
    have ⟨_r, hr⟩ := hstr y hy _ (hf y hyx)
    ih y hyx _ hr.1 ⟨str, hr.2, hstr⟩

private theorem IsLeftWinning.not_isRightSurviving {x : LGame} (h : IsLeftWinning x) :
    ∀ y ∈ x.rightMoves, ¬ IsRightSurviving y :=
  h.rec fun _x _f hf _ ih y hyx ⟨str, hy, hstr⟩ ↦
    have ⟨_r, hr⟩ := hstr y hy _ (hf y hyx)
    ih y hyx _ hr.1 ⟨str, hr.2, hstr⟩

theorem isLeftSuriving_iff_not_isLeftLosing {x : LGame} : IsLeftSurviving x ↔ ¬ IsLeftLosing x where
  mp := fun ⟨str, mem, hstr⟩ ⟨y, hyx, hy⟩ ↦
    have ⟨r, hry, hr⟩ := hstr x mem y hyx
    hy.not_isLeftSurviving r hry ⟨str, hr, hstr⟩
  mpr h := ⟨_, h, leftStrategy_not_isLeftLosing⟩

theorem isRightSuriving_iff_not_isRightLosing {x : LGame} :
    IsRightSurviving x ↔ ¬ IsRightLosing x where
  mp := fun ⟨str, mem, hstr⟩ ⟨y, hyx, hy⟩ ↦
    have ⟨r, hry, hr⟩ := hstr x mem y hyx
    hy.not_isRightSurviving r hry ⟨str, hr, hstr⟩
  mpr h := ⟨_, h, rightStrategy_not_isRightLosing⟩

theorem isLeftSurviving_iff_forall {x : LGame} :
    IsLeftSurviving x ↔ ∀ y ∈ x.rightMoves, ¬ IsRightWinning y := by
  rw [isLeftSuriving_iff_not_isLeftLosing, IsLeftLosing]; push_neg; rfl

theorem isRightSurviving_iff_forall {x : LGame} :
    IsRightSurviving x ↔ ∀ y ∈ x.leftMoves, ¬ IsLeftWinning y := by
  rw [isRightSuriving_iff_not_isRightLosing, IsRightLosing]; push_neg; rfl

theorem left_or_right_survive_left (x : LGame) :
    (∃ y ∈ x.leftMoves, IsLeftSurviving y) ∨ IsRightSurviving x := by
  rw [or_iff_not_imp_left, isRightSurviving_iff_forall]
  push_neg
  exact forall₂_imp fun _ _ ↦ mt (·.isLeftSurviving)

end LGame
