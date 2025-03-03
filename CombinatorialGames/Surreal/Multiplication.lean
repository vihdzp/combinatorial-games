/-
Copyright (c) 2024 Theodore Hwa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kim Morrison, Violeta Hernández Palacios, Junyan Xu, Theodore Hwa
-/
import CombinatorialGames.Surreal.Basic
import Mathlib.Logic.Hydra

/-!
# Surreal multiplication

In this file, we show that multiplication of surreal numbers is well-defined, and thus the
surreal numbers form a linear ordered commutative ring.

An inductive argument proves the following three main theorems:

* P1: being numeric is closed under multiplication,
* P2: multiplying a numeric pregame by equivalent numeric pregames results in equivalent pregames,
* P3: the product of two positive numeric pregames is positive (`mul_pos`).

This is Theorem 8 in [Conway2001], or Theorem 3.8 in [SchleicherStoll]. P1 allows us to define
multiplication as an operation on numeric pregames, P2 says that this is well-defined as an
operation on the quotient by `PGame.Equiv`, namely the surreal numbers, and P3 is an axiom that
needs to be satisfied for the surreals to be a `OrderedRing`.

We follow the proof in [SchleicherStoll], except that we use the well-foundedness of
the hydra relation `CutExpand` on `Multiset PGame` instead of the argument based
on a depth function in the paper.

In the argument, P3 is stated with four variables `x₁`, `x₂`, `y₁`, `y₂` satisfying `x₁ < x₂` and
`y₁ < y₂`, and says that `x₁ * y₂ + x₂ * x₁ < x₁ * y₁ + x₂ * y₂`, which is equivalent to
`0 < x₂ - x₁ → 0 < y₂ - y₁ → 0 < (x₂ - x₁) * (y₂ - y₁)`, i.e.
`@mul_pos PGame _ (x₂ - x₁) (y₂ - y₁)`. It has to be stated in this form and not in terms of
`mul_pos` because we need to show P1, P2 and (a specialized form of) P3 simultaneously, and
for example `P1 x y` will be deduced from P3 with variables taking values simpler than `x` or `y`
(among other induction hypotheses), but if you subtract two pregames simpler than `x` or `y`,
the result may no longer be simpler.

The specialized version of P3 is called P4, which takes only three arguments `x₁`, `x₂`, `y` and
requires that `y₂ = y` or `-y` and that `y₁` is a left option of `y₂`. After P1, P2 and P4 are
shown, a further inductive argument (this time using the `GameAdd` relation) proves P3 in full.

Implementation strategy of the inductive argument: we

* extract specialized versions (`IH1`, `IH2`, `IH3`, `IH4` and `IH24`) of the induction hypothesis
  that are easier to apply (taking `IsOption` arguments directly), and
* show they are invariant under certain symmetries (permutation and negation of arguments) and that
  the induction hypothesis indeed implies the specialized versions.
* utilize the symmetries to minimize calculation.

The whole proof features a clear separation into lemmas of different roles:

* verification of symmetry properties of P and IH (`P3_comm`, `ih1_neg_left`, etc.),
* calculations that connect P1, P2, P3, and inequalities between the product of
  two surreals and its options (`mulOption_lt_iff_P1`, etc.),
* specializations of the induction hypothesis
  (`numeric_option_mul`, `ih1`, `ih1_swap`, `ih₁₂`, `ih4`, etc.),
* application of specialized induction hypothesis
  (`P1_of_ih`, `mul_right_le_of_equiv`, `P3_of_lt`, etc.).
-/

universe u

open IGame Game WellFounded

namespace Surreal.Multiplication

/-! #### Propositions -/

/-- The nontrivial part of P1 in [SchleicherStoll] says that the left options of `x * y` are less
than the right options, and this is the general form of these statements. -/
def P1 (x₁ x₂ x₃ y₁ y₂ y₃ : IGame) : Prop :=
  Game.mk (x₁ * y₁) + Game.mk (x₂ * y₂) - Game.mk (x₁ * y₂) <
    Game.mk (x₃ * y₁) + Game.mk (x₂ * y₃) - Game.mk (x₃ * y₃)

/-- The proposition P2, without numericity assumptions. -/
def P2 (x₁ x₂ y : IGame) : Prop := x₁ ≈ x₂ → Game.mk (x₁ * y) = Game.mk (x₂ * y)

/-- The proposition P3, without the `x₁ < x₂` and `y₁ < y₂` assumptions. -/
def P3 (x₁ x₂ y₁ y₂ : IGame) : Prop :=
  Game.mk (x₁ * y₂) + Game.mk (x₂ * y₁) < Game.mk (x₁ * y₁) + Game.mk (x₂ * y₂)

/-- The proposition P4, without numericity assumptions.

In the references, the second part of the conjunction is stated as
`∀ z ∈ y.rightMoves, P3 x₁ x₂ y z`, which is equivalent to our statement by `P3_comm` and `P3_neg`.
We choose to state everything in terms of left options for uniform treatment. -/
def P4 (x₁ x₂ y : IGame) := x₁ < x₂ →
  (∀ z ∈ y.leftMoves, P3 x₁ x₂ z y) ∧ (∀ z ∈ (-y).leftMoves, P3 x₁ x₂ z (-y))

/-- The conjunction of P2 and P4. -/
def P24 (x₁ x₂ y : IGame) : Prop := P2 x₁ x₂ y ∧ P4 x₁ x₂ y

variable {x x₁ x₂ x₃ x' y y₁ y₂ y₃ y' : IGame}

/-! #### Symmetry properties of P1, P2, P3, and P4 -/

lemma P3_comm : P3 x₁ x₂ y₁ y₂ ↔ P3 y₁ y₂ x₁ x₂ := by
  simp [P3, add_comm, mul_comm]

lemma P3.trans (h₁ : P3 x₁ x₂ y₁ y₂) (h₂ : P3 x₂ x₃ y₁ y₂) : P3 x₁ x₃ y₁ y₂ := by
  rw [P3, ← add_lt_add_iff_left (Game.mk (x₂ * y₁) + Game.mk (x₂ * y₂))]
  convert add_lt_add h₁ h₂ using 1 <;> abel

-- TODO: can I swap the order and make them simp lemmas?

lemma P3_neg : P3 x₁ x₂ y₁ y₂ ↔ P3 (-x₂) (-x₁) y₁ y₂ := by
  simp_rw [P3, neg_mul, Game.mk_neg]
  rw [← neg_lt_neg_iff]
  abel_nf

lemma P2_neg_left : P2 x₁ x₂ y ↔ P2 (-x₂) (-x₁) y := by simp [P2, antisymmRel_comm, eq_comm]
lemma P2_neg_right : P2 x₁ x₂ y ↔ P2 x₁ x₂ (-y) := by simp [P2]

lemma P4_neg_left : P4 x₁ x₂ y ↔ P4 (-x₂) (-x₁) y := by
  simp_rw [P4, IGame.neg_lt_neg_iff, leftMoves_neg, ← P3_neg]

lemma P4_neg_right : P4 x₁ x₂ y ↔ P4 x₁ x₂ (-y) := by
  rw [P4, P4, neg_neg, and_comm]

lemma P24_neg_left : P24 x₁ x₂ y ↔ P24 (-x₂) (-x₁) y := by rw [P24, P24, P2_neg_left, P4_neg_left]
lemma P24_neg_right : P24 x₁ x₂ y ↔ P24 x₁ x₂ (-y) := by rw [P24, P24, P2_neg_right, P4_neg_right]

/-! #### Explicit calculations necessary for the main proof -/

lemma mulOption_lt_iff_P1 {a b c d} :
    Game.mk (mulOption x y a c) < -Game.mk (mulOption x (-y) b d) ↔ P1 a x b y c (-d) := by
  simp [P1, mulOption]; abel_nf

lemma mulOption_lt_mul_iff_P3 {i j} :
    Game.mk (mulOption x y i j) < Game.mk (x * y) ↔ P3 i x j y := by
  simpa [mulOption] using sub_lt_iff_lt_add'

-- TODO: P1_of_equiv?
lemma P1_of_eq (he : x₁ ≈ x₃) (h₁ : P2 x₁ x₃ y₁) (h₃ : P2 x₁ x₃ y₃) (h3 : P3 x₁ x₂ y₂ y₃) :
    P1 x₁ x₂ x₃ y₁ y₂ y₃ := by
  rw [P1, ← h₁ he, ← h₃ he, sub_lt_sub_iff]
  convert add_lt_add_left h3 (Game.mk (x₁ * y₁)) using 1 <;> abel

lemma P1_of_lt (h₁ : P3 x₃ x₂ y₂ y₃) (h₂ : P3 x₁ x₃ y₂ y₁) : P1 x₁ x₂ x₃ y₁ y₂ y₃ := by
  rw [P1, sub_lt_sub_iff, ← add_lt_add_iff_left (Game.mk (x₃ * y₂))]
  convert add_lt_add h₁ h₂ using 1 <;> abel

/-! #### Argument lists -/

/-- The type of lists of arguments for P1, P2, and P4. -/
inductive Args : Type (u + 1)
  | P1 (x y : IGame.{u}) : Args
  | P24 (x₁ x₂ y : IGame.{u}) : Args

/-- The multiset associated to a list of arguments. -/
def Args.toMultiset : Args → Multiset IGame
  | (Args.P1 x y) => {x, y}
  | (Args.P24 x₁ x₂ y) => {x₁, x₂, y}

/-- A list of arguments is numeric if all the arguments are. -/
def Args.Numeric (a : Args) := ∀ x ∈ a.toMultiset, x.Numeric

lemma Args.numeric_P1 {x y} : (Args.P1 x y).Numeric ↔ x.Numeric ∧ y.Numeric := by
  simp [Args.Numeric, Args.toMultiset]

lemma Args.numeric_P24 {x₁ x₂ y} :
    (Args.P24 x₁ x₂ y).Numeric ↔ x₁.Numeric ∧ x₂.Numeric ∧ y.Numeric := by
  simp [Args.Numeric, Args.toMultiset]

open Relation

/-- The relation specifying when a list of (game) arguments is considered simpler than another:
`ArgsRel a₁ a₂` is true if `a₁`, considered as a multiset, can be obtained from `a₂` by repeatedly
removing a game from `a₂` and adding back one or two options of the game. -/
def ArgsRel := InvImage (TransGen <| CutExpand IsOption) Args.toMultiset

/-- `ArgsRel` is well-founded. -/
theorem argsRel_wf : WellFounded ArgsRel := InvImage.wf _ isOption_wf.cutExpand.transGen

/-- The statement that we will show by induction using the well-founded relation `ArgsRel`. -/
def P124 : Args → Prop
  | (Args.P1 x y) => Numeric (x * y)
  | (Args.P24 x₁ x₂ y) => P24 x₁ x₂ y

/-- The property that all arguments are numeric is leftward-closed under `ArgsRel`. -/
lemma ArgsRel.numeric_closed {a' a} : ArgsRel a' a → a.Numeric → a'.Numeric :=
  TransGen.closed' <| @cutExpand_closed _ IsOption ⟨isOption_wf.isIrrefl.1⟩ _
    fun h h' ↦ h'.isOption h

/-- A specialized induction hypothesis used to prove P1. -/
def IH1 (x y : IGame) : Prop :=
  ∀ ⦃x₁ x₂ y'⦄, IsOption x₁ x → IsOption x₂ x → (y' = y ∨ IsOption y' y) → P24 x₁ x₂ y'

/-! #### Symmetry properties of `IH1` -/

lemma ih1_neg_left (h : IH1 x y) : IH1 (-x) y := by
  intro x₁ x₂ y' h₁ h₂ hy
  rw [isOption_neg] at h₁ h₂
  exact P24_neg_left.2 (h h₂ h₁ hy)

lemma ih1_neg_right (h : IH1 x y) : IH1 x (-y) := by
  intro x₁ x₂ y'
  rw [← neg_eq_iff_eq_neg, isOption_neg, P24_neg_right]
  apply h

/-! #### Specialize `ih` to obtain specialized induction hypotheses for P1 -/

lemma numeric_option_mul (ih : ∀ a, ArgsRel a (Args.P1 x y) → P124 a) (h : IsOption x' x) :
    (x' * y).Numeric :=
  ih (Args.P1 x' y) (TransGen.single <| cutExpand_pair_left h)

lemma numeric_mul_option (ih : ∀ a, ArgsRel a (Args.P1 x y) → P124 a) (h : IsOption y' y) :
    (x * y').Numeric :=
  ih (Args.P1 x y') (TransGen.single <| cutExpand_pair_right h)

lemma numeric_option_mul_option (ih : ∀ a, ArgsRel a (Args.P1 x y) → P124 a) (hx : IsOption x' x)
    (hy : IsOption y' y) : (x' * y').Numeric :=
  ih (Args.P1 x' y') ((TransGen.single <| cutExpand_pair_right hy).tail <| cutExpand_pair_left hx)

lemma ih1 (ih : ∀ a, ArgsRel a (Args.P1 x y) → P124 a) : IH1 x y := by
  rintro x₁ x₂ y' h₁ h₂ (rfl|hy) <;> apply ih (Args.P24 _ _ _)
  on_goal 2 => refine TransGen.tail ?_ (cutExpand_pair_right hy)
  all_goals exact TransGen.single (cutExpand_double_left h₁ h₂)

lemma ih1_swap (ih : ∀ a, ArgsRel a (Args.P1 x y) → P124 a) : IH1 y x := ih1 <| by
  simp_rw [ArgsRel, InvImage, Args.toMultiset, Multiset.pair_comm] at ih ⊢
  exact ih

lemma P3_of_ih [Numeric y] (ihyx : IH1 y x) {a b c}
    (ha : a ∈ x.leftMoves) (hb : b ∈ y.leftMoves) (hc : c ∈ (-y).leftMoves) : P3 a x b (-c) := by
  rw [leftMoves_neg] at hc
  rw [← P3_comm]
  refine ((ihyx (.of_mem_leftMoves hb) (.of_mem_rightMoves hc) <| Or.inl rfl).2 ?_).1 a ha
  simpa using Numeric.leftMove_lt_rightMove hb hc

lemma P24_of_ih (ihxy : IH1 x y) {a b} (ha : a ∈ x.leftMoves) (hb : b ∈ x.leftMoves) : P24 a b y :=
  ihxy (.of_mem_leftMoves ha) (.of_mem_leftMoves hb) (Or.inl rfl)

section

lemma mulOption_lt_of_lt [Numeric y] (ihxy : IH1 x y) (ihyx : IH1 y x) {a b c d}
    (ha : a ∈ x.leftMoves) (hb : b ∈ x.leftMoves) (hc : c ∈ y.leftMoves) (hd : d ∈ (-y).leftMoves)
    (h : a < b) : Game.mk (mulOption x y a c) < -Game.mk (mulOption x (-y) b d) :=
  mulOption_lt_iff_P1.2 <| P1_of_lt (P3_of_ih ihyx hb hc hd) <| ((P24_of_ih ihxy ha hb).2 h).1 c hc

lemma mulOption_lt [Numeric x] [Numeric y] (ihxy : IH1 x y) (ihyx : IH1 y x) {a b c d}
    (ha : a ∈ x.leftMoves) (hb : b ∈ x.leftMoves) (hc : c ∈ y.leftMoves) (hd : d ∈ (-y).leftMoves) :
    Game.mk (mulOption x y a c) < -Game.mk (mulOption x (-y) b d) := by
  have : Numeric a := .of_mem_leftMoves ha
  have : Numeric b := .of_mem_leftMoves hb
  obtain (h | h | h) := Numeric.lt_or_equiv_or_gt a b
  · exact mulOption_lt_of_lt ihxy ihyx ha hb hc hd h
  · refine mulOption_lt_iff_P1.2 (P1_of_eq h (P24_of_ih ihxy ha hb).1
      (ihxy ?_ ?_ <| .inr (isOption_neg.1 ?_)).1 <| P3_of_ih ihyx ha hc hd) <;>
      apply IsOption.of_mem_leftMoves <;> assumption
  · rw [lt_neg]
    convert mulOption_lt_of_lt (ih1_neg_right ihxy) (ih1_neg_left ihyx) hb ha hd ?_ h <;> simp_all

end

/-- P1 follows from the induction hypothesis. -/
theorem P1_of_ih (ih : ∀ a, ArgsRel a (Args.P1 x y) → P124 a) (hx : x.Numeric) (hy : y.Numeric) :
    (x * y).Numeric := by
  have ihxy := ih1 ih
  have ihyx := ih1_swap ih
  have ihxyn := ih1_neg_left (ih1_neg_right ihxy)
  have ihyxn := ih1_neg_left (ih1_neg_right ihyx)
  refine numeric_def.mpr ⟨?_, ?_, ?_⟩
  · simp_rw [← Game.mk_lt_mk]
    intro i
    rw [rightMoves_mul]
    simp
    constructor <;> (intro j l; revert i; rw [leftMoves_mul_iff (_ > ·)]; constructor <;> intro i k)
    · apply mulOption_lt hx hy ihxy ihyx
    · simp_rw [← mulOption_symm (-y), mulOption_neg_neg x]
      apply mulOption_lt hy.neg hx.neg ihyxn ihxyn
    · simp only [← mulOption_symm y]
      apply mulOption_lt hy hx ihyx ihxy
    · rw [mulOption_neg_neg y]
      apply mulOption_lt hx.neg hy.neg ihxyn ihyxn
  all_goals
    cases x; cases y
    rintro (⟨i,j⟩|⟨i,j⟩) <;>
    refine ((numeric_option_mul ih ?_).add <| numeric_mul_option ih ?_).sub
      (numeric_option_mul_option ih ?_ ?_) <;>
    solve_by_elim [IsOption.mk_left, IsOption.mk_right]

#exit
/-- A specialized induction hypothesis used to prove P2 and P4. -/
def IH24 (x₁ x₂ y : PGame) : Prop :=
  ∀ ⦃z⦄, (IsOption z x₁ → P24 z x₂ y) ∧ (IsOption z x₂ → P24 x₁ z y) ∧ (IsOption z y → P24 x₁ x₂ z)

/-- A specialized induction hypothesis used to prove P4. -/
def IH4 (x₁ x₂ y : PGame) : Prop :=
  ∀ ⦃z w⦄, IsOption w y → (IsOption z x₁ → P2 z x₂ w) ∧ (IsOption z x₂ → P2 x₁ z w)

/-! #### Specialize `ih'` to obtain specialized induction hypotheses for P2 and P4 -/

lemma ih₁₂ (ih' : ∀ a, ArgsRel a (Args.P24 x₁ x₂ y) → P124 a) : IH24 x₁ x₂ y := by
  rw [IH24]
  refine fun z ↦ ⟨?_, ?_, ?_⟩ <;>
    refine fun h ↦ ih' (Args.P24 _ _ _) (TransGen.single ?_)
  · exact (cutExpand_add_right {y}).2 (cutExpand_pair_left h)
  · exact (cutExpand_add_left {x₁}).2 (cutExpand_pair_left h)
  · exact (cutExpand_add_left {x₁}).2 (cutExpand_pair_right h)

lemma ih₂₁ (ih' : ∀ a, ArgsRel a (Args.P24 x₁ x₂ y) → P124 a) : IH24 x₂ x₁ y := ih₁₂ <| by
  simp_rw [ArgsRel, InvImage, Args.toMultiset, Multiset.pair_comm] at ih' ⊢
  suffices {x₁, y, x₂} = {x₂, y, x₁} by rwa [← this]
  dsimp only [Multiset.insert_eq_cons, ← Multiset.singleton_add] at ih' ⊢
  abel

lemma ih4 (ih' : ∀ a, ArgsRel a (Args.P24 x₁ x₂ y) → P124 a) : IH4 x₁ x₂ y := by
  refine fun z w h ↦ ⟨?_, ?_⟩
  all_goals
    intro h'
    apply (ih' (Args.P24 _ _ _) <| (TransGen.single _).tail <|
      (cutExpand_add_left {x₁}).2 <| cutExpand_pair_right h).1
    try exact (cutExpand_add_right {w}).2 <| cutExpand_pair_left h'
    try exact (cutExpand_add_right {w}).2 <| cutExpand_pair_right h'

lemma numeric_of_ih (ih' : ∀ a, ArgsRel a (Args.P24 x₁ x₂ y) → P124 a) :
    (x₁ * y).Numeric ∧ (x₂ * y).Numeric := by
  constructor <;> refine ih' (Args.P1 _ _) (TransGen.single ?_)
  · exact (cutExpand_add_right {y}).2 <| (cutExpand_add_left {x₁}).2 cutExpand_zero
  · exact (cutExpand_add_right {x₂, y}).2 cutExpand_zero

/-- Symmetry properties of `IH24`. -/
lemma ih24_neg : IH24 x₁ x₂ y → IH24 (-x₂) (-x₁) y ∧ IH24 x₁ x₂ (-y) := by
  simp_rw [IH24, ← P24_neg_right, isOption_neg]
  refine fun h ↦ ⟨fun z ↦ ⟨?_, ?_, ?_⟩,
    fun z ↦ ⟨(@h z).1, (@h z).2.1, P24_neg_right.2 ∘ (@h <| -z).2.2⟩⟩
  all_goals
    rw [P24_neg_left]
    simp only [neg_neg]
    first | exact (@h <| -z).2.1 | exact (@h <| -z).1 | exact (@h z).2.2

/-- Symmetry properties of `IH4`. -/
lemma ih4_neg : IH4 x₁ x₂ y → IH4 (-x₂) (-x₁) y ∧ IH4 x₁ x₂ (-y) := by
  simp_rw [IH4, isOption_neg]
  refine fun h ↦ ⟨fun z w h' ↦ ?_, fun z w h' ↦ ?_⟩
  · convert (h h').symm using 2 <;> rw [P2_neg_left, neg_neg]
  · convert h h' using 2 <;> rw [P2_neg_right]

lemma mulOption_lt_mul_of_equiv (hn : x₁.Numeric) (h : IH24 x₁ x₂ y) (he : x₁ ≈ x₂) (i j) :
    ⟦mulOption x₁ y i j⟧ < (⟦x₂ * y⟧ : Game) := by
  convert sub_lt_iff_lt_add'.2 ((((@h _).1 <| IsOption.moveLeft i).2 _).1 j) using 1
  · rw [← ((@h _).2.2 <| IsOption.moveLeft j).1 he]
    rfl
  · rw [← he.lt_congr_right]
    apply hn.moveLeft_lt

/-- P2 follows from specialized induction hypotheses (one half of the equality). -/
theorem mul_right_le_of_equiv (h₁ : x₁.Numeric) (h₂ : x₂.Numeric)
    (h₁₂ : IH24 x₁ x₂ y) (h₂₁ : IH24 x₂ x₁ y) (he : x₁ ≈ x₂) : x₁ * y ≤ x₂ * y := by
  have he' := neg_equiv_neg_iff.2 he
  apply PGame.le_of_forall_lt <;> simp_rw [lt_iff_game_lt]
  · rw [leftMoves_mul_iff (_ > ·)]
    refine ⟨mulOption_lt_mul_of_equiv h₁ h₁₂ he, ?_⟩
    rw [← quot_neg_mul_neg]
    exact mulOption_lt_mul_of_equiv h₁.neg (ih24_neg <| (ih24_neg h₂₁).1).2 he'
  · rw [rightMoves_mul_iff]
    constructor <;> intros <;> rw [lt_neg]
    · rw [← quot_mul_neg]
      apply mulOption_lt_mul_of_equiv h₂ (ih24_neg h₂₁).2 (symm he)
    · rw [← quot_neg_mul]
      apply mulOption_lt_mul_of_equiv h₂.neg (ih24_neg h₁₂).1 (symm he')

/-- The statement that all left options of `x * y` of the first kind are less than itself. -/
def MulOptionsLTMul (x y : PGame) : Prop := ∀ ⦃i j⦄, ⟦mulOption x y i j⟧ < (⟦x * y⟧ : Game)

/-- That the left options of `x * y` are less than itself and the right options are greater, which
  is part of the condition that `x * y` is numeric, is equivalent to the conjunction of various
  `MulOptionsLTMul` statements for `x`, `y` and their negations. We only show the forward
  direction. -/
lemma mulOptionsLTMul_of_numeric (hn : (x * y).Numeric) :
    (MulOptionsLTMul x y ∧ MulOptionsLTMul (-x) (-y)) ∧
    (MulOptionsLTMul x (-y) ∧ MulOptionsLTMul (-x) y) := by
  constructor
  · have h := hn.moveLeft_lt
    simp_rw [lt_iff_game_lt] at h
    convert (leftMoves_mul_iff <| GT.gt _).1 h
    rw [← quot_neg_mul_neg]
    rfl
  · have h := hn.lt_moveRight
    simp_rw [lt_iff_game_lt, rightMoves_mul_iff] at h
    refine h.imp ?_ ?_ <;> refine forall₂_imp fun a b ↦ ?_
    all_goals
      rw [lt_neg]
      first | rw [quot_mul_neg] | rw [quot_neg_mul]
      exact id

/-- A condition just enough to deduce P3, which will always be used with `x'` being a left
  option of `x₂`. When `y₁` is a left option of `y₂`, it can be deduced from induction hypotheses
  `IH24 x₁ x₂ y₂`, `IH4 x₁ x₂ y₂`, and `(x₂ * y₂).Numeric` (`ih3_of_ih`); when `y₁` is
  not necessarily an option of `y₂`, it follows from the induction hypothesis for P3 (with `x₂`
  replaced by a left option `x'`) after the `main` theorem (P124) is established, and is used to
  prove P3 in full (`P3_of_lt_of_lt`). -/
def IH3 (x₁ x' x₂ y₁ y₂ : PGame) : Prop :=
    P2 x₁ x' y₁ ∧ P2 x₁ x' y₂ ∧ P3 x' x₂ y₁ y₂ ∧ (x₁ < x' → P3 x₁ x' y₁ y₂)

lemma ih3_of_ih (h24 : IH24 x₁ x₂ y) (h4 : IH4 x₁ x₂ y) (hl : MulOptionsLTMul x₂ y) (i j) :
    IH3 x₁ (x₂.moveLeft i) x₂ (y.moveLeft j) y :=
  have ml := @IsOption.moveLeft
  have h24 := (@h24 _).2.1 (ml i)
  ⟨(h4 <| ml j).2 (ml i), h24.1, mulOption_lt_mul_iff_P3.1 (@hl i j), fun l ↦ (h24.2 l).1 _⟩

lemma P3_of_le_left {y₁ y₂} (i) (h : IH3 x₁ (x₂.moveLeft i) x₂ y₁ y₂) (hl : x₁ ≤ x₂.moveLeft i) :
    P3 x₁ x₂ y₁ y₂ := by
  obtain (hl|he) := le_iff_lt_or_antisymmRel.1 hl
  · exact (h.2.2.2 hl).trans h.2.2.1
  · rw [P3, h.1 he, h.2.1 he]
    exact h.2.2.1

/-- P3 follows from `IH3` (so P4 (with `y₁` a left option of `y₂`) follows from the induction
  hypothesis). -/
theorem P3_of_lt {y₁ y₂} (h : ∀ i, IH3 x₁ (x₂.moveLeft i) x₂ y₁ y₂)
    (hs : ∀ i, IH3 (-x₂) ((-x₁).moveLeft i) (-x₁) y₁ y₂) (hl : x₁ < x₂) :
    P3 x₁ x₂ y₁ y₂ := by
  obtain (⟨i,hi⟩|⟨i,hi⟩) := lf_iff_exists_le.1 (lf_of_lt hl)
  · exact P3_of_le_left i (h i) hi
  · apply P3_neg.2 <| P3_of_le_left _ (hs (toLeftMovesNeg i)) _
    simpa

/-- The main chunk of Theorem 8 in [Conway2001] / Theorem 3.8 in [SchleicherStoll]. -/
theorem main (a : Args) : a.Numeric → P124 a := by
  apply argsRel_wf.induction a
  intros a ih ha
  replace ih : ∀ a', ArgsRel a' a → P124 a' := fun a' hr ↦ ih a' hr (hr.numeric_closed ha)
  cases a with
  /- P1 -/
  | P1 x y =>
    rw [Args.numeric_P1] at ha
    exact P1_of_ih ih ha.1 ha.2
  | P24 x₁ x₂ y =>
    have h₁₂ := ih₁₂ ih
    have h₂₁ := ih₂₁ ih
    have h4 := ih4 ih
    obtain ⟨h₁₂x, h₁₂y⟩ := ih24_neg h₁₂
    obtain ⟨h4x, h4y⟩ := ih4_neg h4
    refine ⟨fun he ↦ Quotient.sound ?_, fun hl ↦ ?_⟩
    · /- P2 -/
      rw [Args.numeric_P24] at ha
      exact ⟨mul_right_le_of_equiv ha.1 ha.2.1 h₁₂ h₂₁ he,
        mul_right_le_of_equiv ha.2.1 ha.1 h₂₁ h₁₂ (symm he)⟩
    · /- P4 -/
      obtain ⟨hn₁, hn₂⟩ := numeric_of_ih ih
      obtain ⟨⟨h₁, -⟩, h₂, -⟩ := mulOptionsLTMul_of_numeric hn₂
      obtain ⟨⟨-, h₃⟩, -, h₄⟩ := mulOptionsLTMul_of_numeric hn₁
      constructor <;> intro <;> refine P3_of_lt ?_ ?_ hl <;> intro <;> apply ih3_of_ih
      any_goals assumption
      exacts [(ih24_neg h₁₂y).1, (ih4_neg h4y).1]

end Surreal.Multiplication

namespace PGame
open Surreal.Multiplication

variable {x x₁ x₂ y y₁ y₂ : PGame.{u}}

theorem Numeric.mul (hx : x.Numeric) (hy : y.Numeric) : Numeric (x * y) :=
  main _ <| Args.numeric_P1.mpr ⟨hx, hy⟩

theorem P24 (hx₁ : x₁.Numeric) (hx₂ : x₂.Numeric) (hy : y.Numeric) : P24 x₁ x₂ y :=
  main _ <| Args.numeric_P24.mpr ⟨hx₁, hx₂, hy⟩

theorem Equiv.mul_congr_left (hx₁ : x₁.Numeric) (hx₂ : x₂.Numeric) (hy : y.Numeric)
    (he : x₁ ≈ x₂) : x₁ * y ≈ x₂ * y :=
  equiv_iff_game_eq.2 <| (P24 hx₁ hx₂ hy).1 he

theorem Equiv.mul_congr_right (hx : x.Numeric) (hy₁ : y₁.Numeric) (hy₂ : y₂.Numeric)
    (he : y₁ ≈ y₂) : x * y₁ ≈ x * y₂ :=
  .trans (mul_comm_equiv _ _) <| .trans (mul_congr_left hy₁ hy₂ hx he) (mul_comm_equiv _ _)

theorem Equiv.mul_congr (hx₁ : x₁.Numeric) (hx₂ : x₂.Numeric)
    (hy₁ : y₁.Numeric) (hy₂ : y₂.Numeric) (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ * y₁ ≈ x₂ * y₂ :=
  .trans (mul_congr_left hx₁ hx₂ hy₁ hx) (mul_congr_right hx₂ hy₁ hy₂ hy)

open Prod.GameAdd

/-- One additional inductive argument that supplies the last missing part of Theorem 8. -/
theorem P3_of_lt_of_lt (hx₁ : x₁.Numeric) (hx₂ : x₂.Numeric) (hy₁ : y₁.Numeric) (hy₂ : y₂.Numeric)
    (hx : x₁ < x₂) (hy : y₁ < y₂) : P3 x₁ x₂ y₁ y₂ := by
  revert x₁ x₂
  rw [← Prod.forall']
  refine (wf_isOption.prod_gameAdd wf_isOption).fix ?_
  rintro ⟨x₁, x₂⟩ ih hx₁ hx₂ hx
  refine P3_of_lt ?_ ?_ hx <;> intro i
  · have hi := hx₂.moveLeft i
    exact ⟨(P24 hx₁ hi hy₁).1, (P24 hx₁ hi hy₂).1,
      P3_comm.2 <| ((P24 hy₁ hy₂ hx₂).2 hy).1 _,
      ih _ (snd <| IsOption.moveLeft i) hx₁ hi⟩
  · have hi := hx₁.neg.moveLeft i
    exact ⟨(P24 hx₂.neg hi hy₁).1, (P24 hx₂.neg hi hy₂).1,
      P3_comm.2 <| ((P24 hy₁ hy₂ hx₁).2 hy).2 _, by
        rw [moveLeft_neg, ← P3_neg, neg_lt_neg_iff]
        exact ih _ (fst <| IsOption.moveRight _) (hx₁.moveRight _) hx₂⟩

theorem Numeric.mul_pos (hx₁ : x₁.Numeric) (hx₂ : x₂.Numeric) (hp₁ : 0 < x₁) (hp₂ : 0 < x₂) :
    0 < x₁ * x₂ := by
  rw [lt_iff_game_lt]
  have := P3_of_lt_of_lt numeric_zero hx₁ numeric_zero hx₂ hp₁ hp₂
  simp_rw [P3, quot_zero_mul, quot_mul_zero, add_lt_add_iff_left] at this
  exact this

end PGame

namespace Surreal

open PGame.Equiv

noncomputable instance : LinearOrderedCommRing Surreal where
  __ := Surreal.orderedAddCommGroup
  mul := Surreal.lift₂ (fun x y ox oy ↦ ⟦⟨x * y, ox.mul oy⟩⟧)
    (fun ox₁ oy₁ ox₂ oy₂ hx hy ↦ Quotient.sound <| mul_congr ox₁ ox₂ oy₁ oy₂ hx hy)
  mul_assoc := by rintro ⟨_⟩ ⟨_⟩ ⟨_⟩; exact Quotient.sound (mul_assoc_equiv _ _ _)
  one := mk 1 numeric_one
  one_mul := by rintro ⟨_⟩; exact Quotient.sound (one_mul_equiv _)
  mul_one := by rintro ⟨_⟩; exact Quotient.sound (mul_one_equiv _)
  left_distrib := by rintro ⟨_⟩ ⟨_⟩ ⟨_⟩; exact Quotient.sound (left_distrib_equiv _ _ _)
  right_distrib := by rintro ⟨_⟩ ⟨_⟩ ⟨_⟩; exact Quotient.sound (right_distrib_equiv _ _ _)
  mul_comm := by rintro ⟨_⟩ ⟨_⟩; exact Quotient.sound (mul_comm_equiv _ _)
  le := lift₂ (fun x y _ _ ↦ x ≤ y) (fun _ _ _ _ hx hy ↦ propext <| hx.le_congr hy)
  lt := lift₂ (fun x y _ _ ↦ x < y) (fun _ _ _ _ hx hy ↦ propext <| hx.lt_congr hy)
  le_refl := by rintro ⟨_⟩; apply @le_rfl PGame
  le_trans := by rintro ⟨_⟩ ⟨_⟩ ⟨_⟩; apply @le_trans PGame
  lt_iff_le_not_le := by rintro ⟨_⟩ ⟨_⟩; exact lt_iff_le_not_le
  le_antisymm := by rintro ⟨_⟩ ⟨_⟩ h₁ h₂; exact Quotient.sound ⟨h₁, h₂⟩
  add_le_add_left := by rintro ⟨_⟩ ⟨_⟩ hx ⟨_⟩; exact add_le_add_left hx _
  zero_le_one := PGame.zero_lt_one.le
  zero_mul := by rintro ⟨_⟩; exact Quotient.sound (zero_mul_equiv _)
  mul_zero := by rintro ⟨_⟩; exact Quotient.sound (mul_zero_equiv _)
  exists_pair_ne := ⟨0, 1, ne_of_lt PGame.zero_lt_one⟩
  le_total := by rintro ⟨x⟩ ⟨y⟩; exact (le_or_gf x.1 y.1).imp id (fun h ↦ h.le y.2 x.2)
  mul_pos := by rintro ⟨x⟩ ⟨y⟩; exact x.2.mul_pos y.2
  decidableLE := Classical.decRel _

end Surreal
