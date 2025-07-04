/-
Copyright (c) 2024 Theodore Hwa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kim Morrison, Violeta Hernández Palacios, Junyan Xu, Theodore Hwa
-/
import CombinatorialGames.Surreal.Basic
import Mathlib.Logic.Hydra

/-!
# Surreal multiplication

In this file, we show that multiplication of surreal numbers is well-defined, and thus the surreal
numbers form a linear ordered commutative ring. This is Theorem 8 in [Conway2001], or Theorem 3.8 in
[SchleicherStoll].

An inductive argument proves the following three main theorems:

* P1: being numeric is closed under multiplication,
* P2: multiplying a numeric pregame by equivalent numeric pregames results in equivalent pregames,
* P3: the product of two positive numeric pregames is positive (`mul_pos`).

P1 allows us to define multiplication as an operation on numeric pregames, P2 says that this is
well-defined as an operation on the quotient by `IGame.Equiv`, namely the surreal numbers, and P3 is
an axiom that needs to be satisfied for the surreals to be a `OrderedRing`.

We follow the proof in [SchleicherStoll], except that we use the well-foundedness of the hydra
relation `CutExpand` on `Multiset PGame` instead of the argument based on a depth function in the
paper. As in said argument, P3 is proven by proxy of an auxiliary P4, which states that for
`x₁ < x₂` and `y`, then `x₁ * y + x₂ * a < x₁ * a + x₂ * y` when `a ∈ y.leftMoves`, and
`x₁ * b + x₂ * y < x₁ * y + x₂ * b` when `b ∈ y.rightMoves`.

## Reducing casework

This argument is very casework heavy in a way that's difficult to automate. For instance, in P1, we
have to prove four different inequalities of the form
`a ∈ (x * y).leftMoves → b ∈ (x * y).rightMoves → a < b`, and depending on what form the options of
`x * y` take, we have to apply different instantiations of the inductive hypothesis.

To greatly simplify things, we work uniquely in terms of left options, which we achieve by rewriting
`a ∈ x.rightMoves` as `-a ∈ (-x).leftMoves`. We then show that our distinct lemmas and inductive
hypotheses are invariant under the appropriate sign changes. In the P1 example, this makes it so
that one case (`mulOption_lt_of_lt`) is enough to conclude the others (`mulOption_lt`), and the same
goes for the other parts of the proof.

Note also that we express all inequalities in terms of `Game` instead of `IGame`; this allows us to
make use of `abel` and all of the theorems on `OrderedAddCommGroup`.
-/

universe u

open Game IGame Relation WellFounded

/-- A characterization of left moves of `x * y` in terms only of left moves. -/
private lemma forall_leftMoves_mul' {P : IGame → Prop} {x y : IGame} :
    (∀ a ∈ (x * y).leftMoves, P a) ↔
      (∀ a ∈ x.leftMoves, ∀ b ∈ y.leftMoves, P (mulOption x y a b)) ∧
      (∀ a ∈ (-x).leftMoves, ∀ b ∈ (-y).leftMoves, P (mulOption (-x) (-y) a b)) := by
  simp_rw [forall_leftMoves_mul, leftMoves_neg]
  congr! 1
  rw [← (Equiv.neg _).forall_congr_right]
  congr! 2
  rw [← (Equiv.neg _).forall_congr_right]
  simp [mulOption_neg]

/-- A characterization of right moves of `x * y` in terms only of left moves. -/
private lemma forall_rightMoves_mul' {P : IGame → Prop} {x y : IGame} :
    (∀ a ∈ (x * y).rightMoves, P a) ↔
      (∀ a ∈ x.leftMoves, ∀ b ∈ (-y).leftMoves, P (-mulOption x (-y) a b)) ∧
      (∀ a ∈ (-x).leftMoves, ∀ b ∈ y.leftMoves, P (-mulOption (-x) y a b)) := by
  rw [forall_rightMoves_mul]
  congr! 1
  · congr! 2
    rw [← (Equiv.neg _).forall_congr_right]
    simp [mulOption_neg_right]
  · rw [← (Equiv.neg _).forall_congr_right]
    simp [mulOption_neg_left]

-- Instead of making all of this private, we put it in an auxiliary namespace.
namespace Surreal.Multiplication

/-! ### Predicates P1 – P4 -/

/-- `P1 x y a b c d` means that `mulOption x y a b < mulOption x y c d`. This is the general form
of the statements needed to prove that `x * y` is numeric. -/
def P1 (x y a b c d : IGame) := Game.mk (mulOption x y a b) < Game.mk (mulOption x y c d)

/-- `P2 x₁ x₂ y` states that if `x₁ ≈ x₂`, then `x₁ * y ≈ x₂ * y`. The RHS is stated in terms of
`Game.mk` for rewriting convenience. -/
def P2 (x₁ x₂ y : IGame) := x₁ ≈ x₂ → Game.mk (x₁ * y) = Game.mk (x₂ * y)

/-- `P3 x₁ x₂ y₁ y₂` states that `x₁ * y₂ + x₂ * y₁ < x₁ * y₁ + x₂ * y₂`. Using distributivity, this
is equivalent to `(x₁ - x₂) * (y₁ - y₂) > 0`. -/
def P3 (x₁ x₂ y₁ y₂ : IGame) :=
  Game.mk (x₁ * y₂) + Game.mk (x₂ * y₁) < Game.mk (x₁ * y₁) + Game.mk (x₂ * y₂)

/-- `P4 x₁ x₂ y` states that if `x₁ < x₂`, then `P3 x₁ x₂ a y` when `a ∈ y.leftMoves`, and
`P3 x₁ x₂ b y` when `b ∈ y.rightMoves`.

Note that we instead write this second part as `P3 x₁ x₂ b (-y)` when `b ∈ (-y).leftMoves`. See the
module docstring for an explanation. -/
def P4 (x₁ x₂ y : IGame) :=
  x₁ < x₂ → (∀ a ∈ y.leftMoves, P3 x₁ x₂ a y) ∧ (∀ b ∈ (-y).leftMoves, P3 x₁ x₂ b (-y))

/-- The conjunction of `P2` and `P4`. Both statements have the same amount of arguments and satisfy
similar symmetry properties, so we can slightly simplify the argument by merging them. -/
def P24 (x₁ x₂ y : IGame) : Prop := P2 x₁ x₂ y ∧ P4 x₁ x₂ y

variable {x x₁ x₂ x₃ x' y y₁ y₂ y₃ y' a b c d : IGame.{u}}

/-! #### Symmetry properties of P1 – P4 -/

lemma P3_comm : P3 x₁ x₂ y₁ y₂ ↔ P3 y₁ y₂ x₁ x₂ := by
  simp [P3, add_comm, mul_comm]

lemma P3.trans (h₁ : P3 x₁ x₂ y₁ y₂) (h₂ : P3 x₂ x₃ y₁ y₂) : P3 x₁ x₃ y₁ y₂ := by
  rw [P3, ← add_lt_add_iff_left (Game.mk (x₂ * y₁) + Game.mk (x₂ * y₂))]
  convert add_lt_add h₁ h₂ using 1 <;> abel

lemma P3_neg : P3 (-x₂) (-x₁) y₁ y₂ ↔ P3 x₁ x₂ y₁ y₂ := by
  simp_rw [P3, neg_mul, Game.mk_neg]
  rw [← _root_.neg_lt_neg_iff]
  abel_nf

lemma P2_neg_left : P2 (-x₂) (-x₁) y ↔ P2 x₁ x₂ y := by
  simp [P2, AntisymmRel, eq_comm]

lemma P2_neg_right : P2 x₁ x₂ (-y) ↔ P2 x₁ x₂ y := by
  simp [P2]

lemma P4_neg_left : P4 (-x₂) (-x₁) y ↔P4 x₁ x₂ y  := by
  simp_rw [P4, IGame.neg_lt_neg_iff, P3_neg]

lemma P4_neg_right : P4 x₁ x₂ (-y) ↔ P4 x₁ x₂ y := by
  rw [P4, P4, neg_neg, and_comm]

lemma P24_neg_left : P24 (-x₂) (-x₁) y ↔ P24 x₁ x₂ y := by rw [P24, P24, P2_neg_left, P4_neg_left]
lemma P24_neg_right : P24 x₁ x₂ (-y) ↔ P24 x₁ x₂ y := by rw [P24, P24, P2_neg_right, P4_neg_right]

/-! ### Inductive setup -/

/-- The type of lists of arguments for `P1`, `P2`, and `P4`. -/
inductive Args : Type (u + 1)
  | P1 (x y : IGame.{u}) : Args
  | P24 (x₁ x₂ y : IGame.{u}) : Args

/-- The multiset associated to a list of arguments. -/
def Args.toMultiset : Args → Multiset IGame
  | (Args.P1 x y) => {x, y}
  | (Args.P24 x₁ x₂ y) => {x₁, x₂, y}

@[simp] lemma Args.toMultiset_P1 {x y} : (Args.P1 x y).toMultiset = {x, y} := rfl
@[simp] lemma Args.toMultiset_P24 {x₁ x₂ y} : (Args.P24 x₁ x₂ y).toMultiset = {x₁, x₂, y} := rfl

/-- A list of arguments is numeric if all the arguments are. -/
def Args.Numeric (a : Args) := ∀ x ∈ a.toMultiset, x.Numeric

lemma Args.numeric_P1 {x y} : (Args.P1 x y).Numeric ↔ x.Numeric ∧ y.Numeric := by
  simp [Args.Numeric, Args.toMultiset]

lemma Args.numeric_P24 {x₁ x₂ y} :
    (Args.P24 x₁ x₂ y).Numeric ↔ x₁.Numeric ∧ x₂.Numeric ∧ y.Numeric := by
  simp [Args.Numeric, Args.toMultiset]

/-- The well-founded relation specifying when a list of game arguments is considered simpler than
another: `ArgsRel a₁ a₂` is true if `a₁`, considered as a multiset, can be obtained from `a₂` by
repeatedly removing a game from `a₂` and adding back one or two options of the game.

See also `WellFounded.CutExpand`. -/
def ArgsRel := InvImage (TransGen <| CutExpand IsOption) Args.toMultiset

/-- `ArgsRel` is well-founded. -/
lemma argsRel_wf : WellFounded ArgsRel := InvImage.wf _ isOption_wf.cutExpand.transGen
instance : IsWellFounded _ ArgsRel := ⟨argsRel_wf⟩

/-- The property that all arguments are numeric is leftward-closed under `ArgsRel`. -/
lemma ArgsRel.numeric_closed {a' a} : ArgsRel a' a → a.Numeric → a'.Numeric :=
  TransGen.closed' <| @cutExpand_closed _ _ _ _ fun h h' ↦ h'.isOption h

/-- The statement that we will show by induction for all `Numeric` args, using the well-founded
relation `ArgsRel`.

The inductive hypothesis in the proof will be `∀ a', ArgsRel a' a → P124 a`. -/
def P124 : Args → Prop
  | (Args.P1 x y) => Numeric (x * y)
  | (Args.P24 x₁ x₂ y) => P24 x₁ x₂ y

/-! ### P1 follows from the inductive hypothesis -/

lemma numeric_isOption_mul_of_IH (IH : ∀ a, ArgsRel a (Args.P1 x y) → P124 a) (h : IsOption x' x) :
    (x' * y).Numeric :=
  IH (Args.P1 x' y) (TransGen.single <| cutExpand_pair_left h)

lemma numeric_mul_isOption_of_IH (IH : ∀ a, ArgsRel a (Args.P1 x y) → P124 a) (h : IsOption y' y) :
    (x * y').Numeric :=
  IH (Args.P1 x y') (TransGen.single <| cutExpand_pair_right h)

lemma numeric_isOption_mul_isOption_of_IH (IH : ∀ a, ArgsRel a (Args.P1 x y) → P124 a)
    (hx : IsOption x' x) (hy : IsOption y' y) : (x' * y').Numeric :=
  IH (Args.P1 x' y') ((TransGen.single <| cutExpand_pair_right hy).tail <| cutExpand_pair_left hx)

/-- A specialization of the inductive hypothesis used to prove `P1`. -/
def IH1 (x y : IGame) : Prop :=
  ∀ ⦃x₁ x₂ y'⦄, IsOption x₁ x → IsOption x₂ x → (y' = y ∨ IsOption y' y) → P24 x₁ x₂ y'

/-- `IH1 x y` follows from the inductive hypothesis for `P1 x y`. -/
lemma IH1_of_IH (IH : ∀ a, ArgsRel a (Args.P1 x y) → P124 a) : IH1 x y := by
  rintro x₁ x₂ y' h₁ h₂ (rfl | hy) <;> apply IH (.P24 ..)
  on_goal 2 => refine .tail ?_ (cutExpand_pair_right hy)
  all_goals exact .single (cutExpand_double_left h₁ h₂)

/-- `IH1 y x` follows from the inductive hypothesis for `P1 x y`. -/
lemma IH1_swap_of_IH (IH : ∀ a, ArgsRel a (Args.P1 x y) → P124 a) : IH1 y x := IH1_of_IH <| by
  simpa [-Multiset.insert_eq_cons, ArgsRel, InvImage, Multiset.pair_comm] using IH

lemma IH1_neg_left : IH1 x y → IH1 (-x) y := by
  intro h x₁ x₂ y' h₁ h₂ hy
  rw [isOption_neg] at h₁ h₂
  exact P24_neg_left.1 (h h₂ h₁ hy)

lemma IH1_neg_right : IH1 x y → IH1 x (-y) := by
  intro h x₁ x₂ y'
  rw [← neg_eq_iff_eq_neg, isOption_neg, ← P24_neg_right]
  apply h

lemma P1_of_equiv (he : x₁ ≈ x₃) (h₁ : P2 x₁ x₃ y₁) (h₃ : P2 x₁ x₃ y₃) (h3 : P3 x₁ x₂ y₂ y₃) :
    P1 x₂ y₁ x₁ y₂ x₃ y₃ := by
  rw [P1, mk_mulOption, mk_mulOption, ← h₁ he, ← h₃ he, sub_lt_sub_iff]
  convert add_lt_add_left h3 (.mk (x₁ * y₁)) using 1 <;> abel

lemma P1_of_P3 (h₁ : P3 x₃ x₂ y₂ y₃) (h₂ : P3 x₁ x₃ y₂ y₁) : P1 x₂ y₁ x₁ y₂ x₃ y₃ := by
  rw [P1, mk_mulOption, mk_mulOption, sub_lt_sub_iff, ← add_lt_add_iff_left (.mk (x₃ * y₂))]
  convert add_lt_add h₁ h₂ using 1 <;> abel

lemma P3_of_IH1 [Numeric y] (ihyx : IH1 y x)
    (ha : a ∈ x.leftMoves) (hb : b ∈ y.leftMoves) (hd : d ∈ (-y).leftMoves) : P3 a x b (-d) := by
  rw [P3_comm]
  rw [leftMoves_neg] at hd
  refine ((ihyx (.of_mem_leftMoves hb) (.of_mem_rightMoves hd) <| Or.inl rfl).2 ?_).1 a ha
  exact Numeric.leftMove_lt_rightMove hb hd

lemma P24_of_IH1 (ihxy : IH1 x y) (ha : a ∈ x.leftMoves) (hb : b ∈ x.leftMoves) : P24 a b y :=
  ihxy (.of_mem_leftMoves ha) (.of_mem_leftMoves hb) (Or.inl rfl)

lemma mulOption_lt_iff_P1 :
    Game.mk (mulOption x y a b) < -Game.mk (mulOption x (-y) c d) ↔ P1 x y a b c (-d) := by
  simp [P1, mulOption, sub_eq_add_neg, add_comm]

lemma mulOption_lt_of_lt [Numeric y] (ihxy : IH1 x y) (ihyx : IH1 y x) {a b c d} (h : a < c)
    (ha : a ∈ x.leftMoves) (hb : b ∈ y.leftMoves) (hc : c ∈ x.leftMoves) (hd : d ∈ (-y).leftMoves) :
    Game.mk (mulOption x y a b) < -Game.mk (mulOption x (-y) c d) := by
  rw [mulOption_lt_iff_P1]
  exact P1_of_P3 (P3_of_IH1 ihyx hc hb hd) <| ((P24_of_IH1 ihxy ha hc).2 h).1 b hb

lemma mulOption_lt [Numeric x] [Numeric y] (ihxy : IH1 x y) (ihyx : IH1 y x) {a b c d}
    (ha : a ∈ x.leftMoves) (hb : b ∈ y.leftMoves) (hc : c ∈ x.leftMoves) (hd : d ∈ (-y).leftMoves) :
    Game.mk (mulOption x y a b) < -Game.mk (mulOption x (-y) c d) := by
  have := Numeric.of_mem_leftMoves ha
  have := Numeric.of_mem_leftMoves hc
  obtain (h | h | h) := Numeric.lt_or_equiv_or_gt a c
  · exact mulOption_lt_of_lt ihxy ihyx h ha hb hc hd
  · refine mulOption_lt_iff_P1.2 (P1_of_equiv h (P24_of_IH1 ihxy ha hc).1
      (ihxy ?_ ?_ <| .inr (isOption_neg.1 ?_)).1 <| P3_of_IH1 ihyx ha hb hd)
    all_goals apply IsOption.of_mem_leftMoves; assumption
  · rw [← neg_neg y] at hb
    simpa [lt_neg] using mulOption_lt_of_lt (IH1_neg_right ihxy) (IH1_neg_left ihyx) h hc hd ha hb

/-- `P1` follows from the induction hypothesis. -/
lemma P1_of_IH (IH : ∀ a, ArgsRel a (Args.P1 x y) → P124 a) [Numeric x] [Numeric y] :
    (x * y).Numeric := by
  have ihxy := IH1_of_IH IH
  have ihyx := IH1_swap_of_IH IH
  have ihxyn := IH1_neg_left (IH1_neg_right ihxy)
  have ihyxn := IH1_neg_left (IH1_neg_right ihyx)
  refine .mk' ?_ ?_ ?_
  · simp_rw [forall_leftMoves_mul', forall_rightMoves_mul']
    constructor <;> intro a ha b hb <;> constructor <;> intro c hc d hd
    · exact mulOption_lt ihxy ihyx ha hb hc hd
    · simpa [mulOption_comm] using mulOption_lt ihyx ihxy hb ha hd hc
    · rw [← neg_neg x] at hc
      simpa [mulOption_comm] using mulOption_lt ihyxn ihxyn hb ha hd hc
    · rw [← neg_neg y] at hd
      simpa using mulOption_lt ihxyn ihyxn ha hb hc hd
  all_goals
    simp only [leftMoves_mul, rightMoves_mul, mulOption, Set.mem_image, Prod.exists,
      forall_exists_index, and_imp]
    rintro _ a b (⟨ha, hb⟩ | ⟨ha, hb⟩) rfl
    all_goals
      try replace ha := IsOption.of_mem_leftMoves ha
      try replace ha := IsOption.of_mem_rightMoves ha
      try replace hb := IsOption.of_mem_leftMoves hb
      try replace hb := IsOption.of_mem_rightMoves hb
      have := numeric_isOption_mul_of_IH IH ha
      have := numeric_mul_isOption_of_IH IH hb
      have := numeric_isOption_mul_isOption_of_IH IH ha hb
      infer_instance

/-! ### P2 follows from the inductive hypothesis -/

lemma numeric_of_IH (IH : ∀ a, ArgsRel a (Args.P24 x₁ x₂ y) → P124 a) :
    (x₁ * y).Numeric ∧ (x₂ * y).Numeric := by
  constructor <;> refine IH (.P1 ..) (.single ?_)
  · exact (cutExpand_add_right {y}).2 <| (cutExpand_add_left {x₁}).2 cutExpand_zero
  · exact (cutExpand_add_right {x₂, y}).2 cutExpand_zero

/-- A specialization of the inductive hypothesis used to prove `P2` and `P4`. -/
def IH24 (x₁ x₂ y : IGame) : Prop :=
  ∀ ⦃z⦄, (IsOption z x₁ → P24 z x₂ y) ∧ (IsOption z x₂ → P24 x₁ z y) ∧ (IsOption z y → P24 x₁ x₂ z)

/-- A specialization of the induction hypothesis used to prove `P4`. -/
def IH4 (x₁ x₂ y : IGame) : Prop :=
  ∀ ⦃z w⦄, IsOption w y → (IsOption z x₁ → P2 z x₂ w) ∧ (IsOption z x₂ → P2 x₁ z w)

/-- `IH24 x₁ x₂ y` follows from the inductive hypothesis for `P24 x₁ x₂ y`. -/
lemma IH24_of_IH (IH : ∀ a, ArgsRel a (Args.P24 x₁ x₂ y) → P124 a) : IH24 x₁ x₂ y := by
  rw [IH24]
  refine fun z ↦ ⟨?_, ?_, ?_⟩ <;> refine fun h ↦ IH (.P24 ..) (.single ?_)
  · exact (cutExpand_add_right {y}).2 (cutExpand_pair_left h)
  · exact (cutExpand_add_left {x₁}).2 (cutExpand_pair_left h)
  · exact (cutExpand_add_left {x₁}).2 (cutExpand_pair_right h)

/-- `IH24 x₂ x₁ y` follows from the inductive hypothesis for `P24 x₁ x₂ y`. -/
lemma IH24_swap_of_IH (IH : ∀ a, ArgsRel a (Args.P24 x₁ x₂ y) → P124 a) : IH24 x₂ x₁ y := by
  apply IH24_of_IH
  convert IH using 2
  dsimp [ArgsRel, InvImage, Multiset.insert_eq_cons, ← Multiset.singleton_add]
  abel_nf

/-- `IH4 x₁ x₂ y` follows from the inductive hypothesis for `P24 x₁ x₂ y`. -/
lemma IH4_of_IH (IH : ∀ a, ArgsRel a (Args.P24 x₁ x₂ y) → P124 a) : IH4 x₁ x₂ y := by
  refine fun a b h ↦ ⟨?_, ?_⟩ <;>
    refine fun h' ↦ (IH (.P24 ..) <| (TransGen.single ?_).tail <|
      (cutExpand_add_left {x₁}).2 <| cutExpand_pair_right h).1
  · exact (cutExpand_add_right {b}).2 <| cutExpand_pair_left h'
  · exact (cutExpand_add_right {b}).2 <| cutExpand_pair_right h'

lemma IH24_neg : IH24 x₁ x₂ y → IH24 (-x₂) (-x₁) y ∧ IH24 x₁ x₂ (-y) := by
  simp_rw [IH24, P24_neg_right, isOption_neg]
  refine fun (h : ∀ _, _) ↦ ⟨fun z ↦ ⟨?_, ?_, ?_⟩,
    fun z ↦ ⟨(h z).1, (h z).2.1, P24_neg_right.1 ∘ (h (-z)).2.2⟩⟩
  all_goals
    rw [← P24_neg_left]
    simp only [neg_neg]
  · exact (h (-z)).2.1
  · exact (h (-z)).1
  · exact (h z).2.2

lemma IH4_neg : IH4 x₁ x₂ y → IH4 (-x₂) (-x₁) y ∧ IH4 x₁ x₂ (-y) := by
  simp_rw [IH4, isOption_neg]
  refine fun h ↦ ⟨fun z w h' ↦ ?_, fun z w h' ↦ ?_⟩
  · convert (h h').symm using 2 <;> rw [← P2_neg_left, neg_neg]
  · convert h h' using 2 <;> rw [P2_neg_right]

lemma mulOption_lt_mul_of_equiv [Numeric x₁] (h : IH24 x₁ x₂ y) (he : x₁ ≈ x₂)
    (hi : a ∈ x₁.leftMoves) (hj : b ∈ y.leftMoves) :
    Game.mk (mulOption x₁ y a b) < Game.mk (x₂ * y) := by
  convert sub_lt_iff_lt_add'.2 (((h.1 (.of_mem_leftMoves hi)).2 _).1 b hj) using 1
  · rw [← (h.2.2 (.of_mem_leftMoves hj)).1 he]
    rfl
  · rw [← he.lt_congr_right]
    exact Numeric.leftMove_lt hi

lemma mul_right_le_of_equiv [Numeric x₁] [Numeric x₂]
    (ih₁₂ : IH24 x₁ x₂ y) (ih₂₁ : IH24 x₂ x₁ y) (he : x₁ ≈ x₂) : x₁ * y ≤ x₂ * y := by
  have he' := neg_equiv_neg_iff.2 he
  rw [IGame.le_iff_forall_lf]
  simp_rw [← Game.mk_le_mk]
  constructor
  · rw [forall_leftMoves_mul']
    constructor <;> intro a ha b hb
    · exact (mulOption_lt_mul_of_equiv ih₁₂ he ha hb).not_ge
    · simpa using (mulOption_lt_mul_of_equiv (IH24_neg <| (IH24_neg ih₂₁).1).2 he' ha hb).not_ge
  · rw [forall_rightMoves_mul']
    constructor <;> intro a ha b hb
    · simpa [neg_le] using (mulOption_lt_mul_of_equiv (IH24_neg ih₂₁).2 he.symm ha hb).not_ge
    · simpa [neg_le] using (mulOption_lt_mul_of_equiv (IH24_neg ih₁₂).1 he'.symm ha hb).not_ge

/-- `P2` follows from the induction hypothesis. -/
lemma P2_of_IH (IH : ∀ a, ArgsRel a (Args.P24 x₁ x₂ y) → P124 a) [Numeric x₁] [Numeric x₂]
    (he : x₁ ≈ x₂) : x₁ * y ≈ x₂ * y :=
  ⟨mul_right_le_of_equiv (IH24_of_IH IH) (IH24_swap_of_IH IH) he,
    mul_right_le_of_equiv (IH24_swap_of_IH IH) (IH24_of_IH IH) he.symm⟩

/-! ### P4 follows from the inductive hypothesis -/

lemma mulOption_lt_mul_iff_P3 : mulOption x y a b < x * y ↔ P3 a x b y :=
  @sub_lt_iff_lt_add' Game _ _ _ (.mk _) (.mk _) (.mk _)

/-- A specialization of the induction hypothesis used to prove `P3`. -/
def IH3 (x₁ x' x₂ y₁ y₂ : IGame) : Prop :=
  P2 x₁ x' y₁ ∧ P2 x₁ x' y₂ ∧ P3 x' x₂ y₁ y₂ ∧ (x₁ < x' → P3 x₁ x' y₁ y₂)

/-- `IH3` follows from the induction hypothesis for `P24 x₁ x₂ y`. -/
lemma IH3_of_IH (ih24 : IH24 x₁ x₂ y) (ih4 : IH4 x₁ x₂ y)
    (hi : a ∈ x₂.leftMoves) (hb : b ∈ y.leftMoves) (hl : mulOption x₂ y a b < x₂ * y) :
    IH3 x₁ a x₂ b y :=
  have h24 := ih24.2.1 (.of_mem_leftMoves hi)
  ⟨(ih4 <| .of_mem_leftMoves hb).2 (.of_mem_leftMoves hi), h24.1,
    mulOption_lt_mul_iff_P3.1 hl, fun l ↦ (h24.2 l).1 b hb⟩

lemma P3_of_le_left {y₁ y₂} (i) (h : IH3 x₁ i x₂ y₁ y₂) (hl : x₁ ≤ i) : P3 x₁ x₂ y₁ y₂ := by
  obtain (hl | he) := le_iff_lt_or_antisymmRel.1 hl
  · exact (h.2.2.2 hl).trans h.2.2.1
  · rw [P3, h.1 he, h.2.1 he]
    exact h.2.2.1

/-- P3 follows from `IH3`, so P4 (with `y₁` a left option of `y₂`) follows from the induction
hypothesis. -/
lemma P3_of_IH3 {y₁ y₂} (h : ∀ i ∈ x₂.leftMoves, IH3 x₁ i x₂ y₁ y₂)
    (hs : ∀ i ∈ (-x₁).leftMoves, IH3 (-x₂) i (-x₁) y₁ y₂) (hl : x₁ < x₂) : P3 x₁ x₂ y₁ y₂ := by
  obtain (⟨i, hi, hi'⟩ | ⟨i, hi, hi'⟩) := lf_iff_exists_le.1 hl.not_ge
  · exact P3_of_le_left i (h i hi) hi'
  · refine P3_neg.1 <| P3_of_le_left _ (hs (-i) ?_) ?_ <;> simpa

/-- `P4` follows from the induction hypothesis. -/
lemma P4_of_IH (IH : ∀ a, ArgsRel a (.P24 x₁ x₂ y) → P124 a) : P4 x₁ x₂ y := by
  have h₁₂ := IH24_of_IH IH
  have h4 := IH4_of_IH IH
  obtain ⟨h₁₂x, h₁₂y⟩ := IH24_neg h₁₂
  obtain ⟨h4x, h4y⟩ := IH4_neg h4
  have := (IH24_neg h₁₂y).1
  have := (IH4_neg h4y).1
  obtain ⟨hn₁, hn₂⟩ := numeric_of_IH IH
  have : (-x₁ * y).Numeric := by simpa
  have : (-x₁ * -y).Numeric := by simpa
  have : (x₂ * -y).Numeric := by simpa
  refine fun hl ↦ ⟨?_, ?_⟩ <;>
    refine fun a ha ↦ P3_of_IH3 ?_ ?_ hl <;>
    intro b hb <;>
    apply IH3_of_IH
  assumption'
  all_goals
    apply Numeric.leftMove_lt (mulOption_left_left_mem_leftMoves_mul _ _) <;> assumption

/-- We tie everything together to complete the induction. -/
theorem main (a : Args) : a.Numeric → P124 a := by
  apply argsRel_wf.induction a
  intro a IH ha
  replace ih : ∀ a', ArgsRel a' a → P124 a' := fun a' hr ↦ IH a' hr (hr.numeric_closed ha)
  cases a with
  | P1 x y =>
    obtain ⟨_, _⟩ := Args.numeric_P1.1 ha
    exact P1_of_IH ih
  | P24 x₁ x₂ y =>
    obtain ⟨_, _, _⟩ := Args.numeric_P24.1 ha
    constructor
    · exact (Game.mk_eq <| P2_of_IH ih ·)
    · exact P4_of_IH ih

lemma main_P24 (x₁ x₂ y : IGame) [hx₁ : Numeric x₁] [hx₂ : Numeric x₂] [hy : Numeric y] :
    P24 x₁ x₂ y :=
  main _ <| Args.numeric_P24.mpr ⟨hx₁, hx₂, hy⟩

/-- One additional inductive argument proves `P3`. -/
lemma P3_of_lt_of_lt {x₁ x₂ y₁ y₂} [Numeric x₁] [Numeric x₂] [Numeric y₁] [Numeric y₂]
    (hx : x₁ < x₂) (hy : y₁ < y₂) : P3 x₁ x₂ y₁ y₂ := by
  refine P3_of_IH3 ?_ ?_ hx
  all_goals
    intro i hi
    have := Numeric.of_mem_leftMoves hi
    refine ⟨(main_P24 ..).1, (main_P24 ..).1, P3_comm.2 ?_, fun h ↦ ?_⟩
  · exact ((main_P24 y₁ y₂ x₂).2 hy).1 _ hi
  · exact P3_of_lt_of_lt h hy
  · exact ((main_P24 y₁ y₂ x₁).2 hy).2 _ hi
  · rw [IGame.neg_lt] at h
    rw [← P3_neg, neg_neg]
    exact P3_of_lt_of_lt h hy
termination_by (x₁, x₂)
decreasing_by all_goals (try rw [leftMoves_neg] at *); igame_wf

end Surreal.Multiplication

/-! ### Instances and corollaries -/

namespace IGame.Numeric
open Surreal.Multiplication

variable {x x₁ x₂ y y₁ y₂: IGame}

instance mul (x y : IGame) [hx : Numeric x] [hy : Numeric y] : Numeric (x * y) :=
  main _ <| Args.numeric_P1.mpr ⟨hx, hy⟩

protected instance mulOption (x y a b : IGame) [Numeric x] [Numeric y] [Numeric a] [Numeric b] :
    Numeric (mulOption x y a b) :=
  inferInstanceAs (Numeric (_ - _))

theorem mul_congr_left [Numeric x₁] [Numeric x₂] [Numeric y] (he : x₁ ≈ x₂) : x₁ * y ≈ x₂ * y :=
  Game.mk_eq_mk.1 ((main_P24 ..).1 he)

theorem mul_congr_right [Numeric x] [Numeric y₁] [Numeric y₂] (he : y₁ ≈ y₂) : x * y₁ ≈ x * y₂ := by
  rw [mul_comm, mul_comm x]; exact Numeric.mul_congr_left he

theorem mul_congr [Numeric x₁] [Numeric x₂] [Numeric y₁] [Numeric y₂]
    (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ * y₁ ≈ x₂ * y₂ :=
  (mul_congr_left hx).trans (mul_congr_right hy)

theorem mul_pos [Numeric x₁] [Numeric x₂] (hp₁ : 0 < x₁) (hp₂ : 0 < x₂) : 0 < x₁ * x₂ := by
  simpa [P3] using P3_of_lt_of_lt hp₁ hp₂

end IGame.Numeric

namespace Surreal

noncomputable instance : CommRing Surreal where
  mul := Quotient.map₂ (fun a b ↦ ⟨a.1 * b.1, inferInstance⟩) fun _ _ h _ _ ↦ Numeric.mul_congr h
  zero_mul := by rintro ⟨x⟩; change mk (0 * x) = mk 0; simp_rw [zero_mul]
  mul_zero := by rintro ⟨x⟩; change mk (x * 0) = mk 0; simp_rw [mul_zero]
  one_mul := by rintro ⟨x⟩; change mk (1 * x) = mk x; simp_rw [one_mul]
  mul_one := by rintro ⟨x⟩; change mk (x * 1) = mk x; simp_rw [mul_one]
  left_distrib := by rintro ⟨x⟩ ⟨y⟩ ⟨z⟩; exact mk_eq (mul_add_equiv ..)
  right_distrib := by rintro ⟨x⟩ ⟨y⟩ ⟨z⟩; exact mk_eq (add_mul_equiv ..)
  mul_comm := by rintro ⟨x⟩ ⟨y⟩; change mk (x * y) = mk (y * x); simp_rw [mul_comm]
  mul_assoc := by rintro ⟨x⟩ ⟨y⟩ ⟨z⟩; exact mk_eq (mul_assoc_equiv ..)

instance : IsStrictOrderedRing Surreal :=
  .of_mul_pos (by rintro ⟨x⟩ ⟨y⟩; exact Numeric.mul_pos)

@[simp]
theorem mk_mul (x y : IGame) [Numeric x] [Numeric y] :
    Surreal.mk (x * y) = Surreal.mk x * Surreal.mk y :=
  rfl

end Surreal

namespace IGame.Numeric

protected theorem mul_neg_of_pos_of_neg {x y : IGame} [Numeric x] [Numeric y]
    (hx : 0 < x) (hy : y < 0) : x * y < 0 :=
  @mul_neg_of_pos_of_neg Surreal _ (.mk x) (.mk y) _ _ hx hy

protected theorem mul_neg_of_neg_of_pos {x y : IGame} [Numeric x] [Numeric y]
    (hx : x < 0) (hy : 0 < y) : x * y < 0 :=
  @mul_neg_of_neg_of_pos Surreal _ (.mk x) (.mk y) _ _ hx hy

protected theorem mul_pos_of_neg_of_neg {x y : IGame} [Numeric x] [Numeric y]
    (hx : x < 0) (hy : y < 0) : 0 < x * y :=
  @mul_pos_of_neg_of_neg Surreal _ _ _ _ _ _ (.mk x) (.mk y) hx hy

protected theorem mul_nonneg {x y : IGame} [Numeric x] [Numeric y]
    (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x * y :=
  @mul_nonneg Surreal _ (.mk x) (.mk y) _ _ hx hy

protected theorem mul_nonpos_of_nonneg_of_nonpos {x y : IGame} [Numeric x] [Numeric y]
    (hx : 0 ≤ x) (hy : y ≤ 0) : x * y ≤ 0 :=
  @mul_nonpos_of_nonneg_of_nonpos Surreal _ (.mk x) (.mk y) _ _ hx hy

protected theorem mul_nonpos_of_nonpos_of_nonneg {x y : IGame} [Numeric x] [Numeric y]
    (hx : x ≤ 0) (hy : 0 ≤ y) : x * y ≤ 0 :=
  @mul_nonpos_of_nonpos_of_nonneg Surreal _ (.mk x) (.mk y) _ _ hx hy

protected theorem mul_nonneg_of_nonpos_of_nonpos {x y : IGame} [Numeric x] [Numeric y]
    (hx : x ≤ 0) (hy : y ≤ 0) : 0 ≤ x * y :=
  @mul_nonneg_of_nonpos_of_nonpos Surreal _ _ (.mk x) (.mk y) _ _ _ _ hx hy

protected theorem mul_left_cancel {x y z : IGame} [Numeric x] [Numeric y] [Numeric z]
    (hx : ¬ x ≈ 0) (h : x * y ≈ x * z) : y ≈ z := by
  rw [← Surreal.mk_eq_mk] at *
  exact mul_left_cancel₀ hx h

protected theorem mul_right_cancel {x y z : IGame} [Numeric x] [Numeric y] [Numeric z]
    (hx : ¬ x ≈ 0) (h : y * x ≈ z * x) : y ≈ z := by
  rw [← Surreal.mk_eq_mk] at *
  exact mul_right_cancel₀ hx h

@[simp]
protected theorem mul_le_mul_left {x y z : IGame} [Numeric x] [Numeric y] [Numeric z]
    (hx : 0 < x) : x * y ≤ x * z ↔ y ≤ z :=
  mul_le_mul_left (a := Surreal.mk x) (b := Surreal.mk y) (c := Surreal.mk z) hx

@[simp]
protected theorem mul_le_mul_right {x y z : IGame} [Numeric x] [Numeric y] [Numeric z]
    (hx : 0 < x) : y * x ≤ z * x ↔ y ≤ z :=
  mul_le_mul_right (a := Surreal.mk x) (b := Surreal.mk y) (c := Surreal.mk z) hx

@[simp]
protected theorem mul_lt_mul_left {x y z : IGame} [Numeric x] [Numeric y] [Numeric z]
    (hx : 0 < x) : x * y < x * z ↔ y < z :=
  mul_lt_mul_left (a := Surreal.mk x) (b := Surreal.mk y) (c := Surreal.mk z) hx

@[simp]
protected theorem mul_lt_mul_right {x y z : IGame} [Numeric x] [Numeric y] [Numeric z]
    (hx : 0 < x) : y * x < z * x ↔ y < z :=
  mul_lt_mul_right (a := Surreal.mk x) (b := Surreal.mk y) (c := Surreal.mk z) hx

@[simp]
protected theorem mul_le_mul_left_of_neg {x y z : IGame} [Numeric x] [Numeric y] [Numeric z]
    (hz : z < 0) : z * x ≤ z * y ↔ y ≤ x :=
  mul_le_mul_left_of_neg (a := Surreal.mk x) (b := Surreal.mk y) (c := Surreal.mk z) hz

@[simp]
protected theorem mul_le_mul_right_of_neg {x y z : IGame} [Numeric x] [Numeric y] [Numeric z]
    (hz : z < 0) : x * z ≤ y * z ↔ y ≤ x :=
  mul_le_mul_right_of_neg (a := Surreal.mk x) (b := Surreal.mk y) (c := Surreal.mk z) hz

@[simp]
protected theorem mul_lt_mul_left_of_neg {x y z : IGame} [Numeric x] [Numeric y] [Numeric z]
    (hz : z < 0) : z * x < z * y ↔ y < x :=
  mul_lt_mul_left_of_neg (a := Surreal.mk x) (b := Surreal.mk y) (c := Surreal.mk z) hz

@[simp]
protected theorem mul_lt_mul_right_of_neg {x y z : IGame} [Numeric x] [Numeric y] [Numeric z]
    (hz : z < 0) : x * z < y * z ↔ y < x :=
  mul_lt_mul_right_of_neg (a := Surreal.mk x) (b := Surreal.mk y) (c := Surreal.mk z) hz

theorem mul_equiv_zero {x y : IGame} [Numeric x] [Numeric y] : x * y ≈ 0 ↔ x ≈ 0 ∨ y ≈ 0 := by
  repeat rw [← Surreal.mk_eq_mk]
  exact @mul_eq_zero Surreal _ _ (.mk x) (.mk y)

theorem mulOption_congr₁ {x₁ x₂ y a b : IGame}
    [Numeric x₁] [Numeric x₂] [Numeric y] [Numeric a] [Numeric b] (he : x₁ ≈ x₂) :
    mulOption x₁ y a b ≈ mulOption x₂ y a b := by
  simp_all [← Surreal.mk_eq_mk, mulOption]

theorem mulOption_congr₂ {x y₁ y₂ a b : IGame}
    [Numeric x] [Numeric y₁] [Numeric y₂] [Numeric a] [Numeric b] (he : y₁ ≈ y₂) :
    mulOption x y₁ a b ≈ mulOption x y₂ a b := by
  simp_all [← Surreal.mk_eq_mk, mulOption]

theorem mulOption_congr₃ {x y a₁ a₂ b : IGame}
    [Numeric x] [Numeric y] [Numeric a₁] [Numeric a₂] [Numeric b] (he : a₁ ≈ a₂) :
    mulOption x y a₁ b ≈ mulOption x y a₂ b := by
  simp_all [← Surreal.mk_eq_mk, mulOption]

theorem mulOption_congr₄ {x y a b₁ b₂ : IGame}
    [Numeric x] [Numeric y] [Numeric a] [Numeric b₁] [Numeric b₂] (he : b₁ ≈ b₂) :
    mulOption x y a b₁ ≈ mulOption x y a b₂ := by
  simp_all [← Surreal.mk_eq_mk, mulOption]

end IGame.Numeric
