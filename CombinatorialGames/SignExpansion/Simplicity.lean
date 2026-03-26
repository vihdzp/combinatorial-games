/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import CombinatorialGames.SignExpansion.Basic

/-!
# Simplicity relation

We define the simplicity relation on sign sequences, i.e. the relation where `x ≤ y` iff `x` is an
initial segment of `y`. In the literature, this is variously denoted as `x ≤ₛ y` or `x ⊏ y`. We also
define supremum and infimum operators.

## Implementation notes

Sign sequences already have a linear ordering given by the lexicographic ordering. Since we can't
define two separate `PartialOrder` instances on the same type, we instead create a type alias
`Simpllicity`, and declare the simplicity ordering on that.
-/

/-! ### For Mathlib -/

-- #37079
open Set in
/-- An alternative constructor for `SemilatticeSup` using `IsLUB`. -/
@[to_dual (attr := implicit_reducible)
/-- An alternative constructor for `SemilatticeInf` using `IsGLB`. -/]
public def SemilatticeSup.ofIsLUB {α} [PartialOrder α] (sup : α → α → α)
    (isLUB_pair : ∀ a b, IsLUB {a, b} (sup a b)) :
    SemilatticeSup α where
  sup := sup
  le_sup_left a b := (isLUB_pair a b).1 (mem_insert _ _)
  le_sup_right a b := (isLUB_pair a b).1 (mem_insert_of_mem _ (mem_singleton _))
  sup_le a b _ hac hbc := (isLUB_pair a b).2 (forall_insert_of_forall (forall_eq.mpr hbc) hac)

@[no_expose, to_dual (attr := implicit_reducible)]
noncomputable def BddBelow.orderBot {α : Type*} [Preorder α] (h : BddBelow (α := α) .univ) :
    OrderBot α := by
  choose a ha using h
  refine { bot := a, bot_le := ?_ }
  simpa [lowerBounds] using ha

@[to_dual]
theorem WithTop.isGLB_of_coe_preimage {α : Type*} [PartialOrder α] {x : α} {s : Set (WithTop α)}
    (hs' : ∃ y : α, ↑y ∈ s) (hs : IsGLB ((↑) ⁻¹' s) x) : IsGLB s x := by
  simpa [isGLB_iff_le_iff, lowerBounds, WithTop.forall, hs'] using hs

@[to_dual]
theorem WithTop.isLUB_of_coe_preimage {α : Type*} [PartialOrder α] {x : α} {s : Set (WithTop α)}
    (hs' : ⊤ ∉ s) (hs : IsLUB ((↑) ⁻¹' s) x) : IsLUB s x := by
  simpa [isLUB_iff_le_iff, upperBounds, WithTop.forall, hs'] using hs

open Classical in
theorem WithTop.isGLB_sInf_of_nonempty {α : Type*} [PartialOrder α] [InfSet α]
    (h : ∀ s : Set α, s.Nonempty → IsGLB s (sInf s)) (s : Set (WithTop α)) : IsGLB s (sInf s) := by
  change IsGLB s (dite ..)
  let := (h _ Set.univ_nonempty).bddBelow.orderBot
  split_ifs with hs
  · rw [Set.subset_singleton_iff_eq] at hs
    aesop
  · apply isGLB_of_coe_preimage _ (h ..)
    · simpa [WithTop.exists] using hs
    · aesop (add simp [WithTop.exists, Set.Nonempty])

@[expose] public noncomputable section

open SignExpansion

/-! ### Type alias -/

/-- A type alias for `SignExpansion`, endowed with the simplicity ordering. -/
def Simplicity : Type _ := SignExpansion
deriving Inhabited

namespace Simplicity

/-- The identity function between `SignExpansion` and `Simplicity`. -/
def of : SignExpansion ≃ Simplicity := Equiv.refl _

/-- The identity function between `Simplicity` and `SignExpansion`. -/
def val : Simplicity ≃ SignExpansion := Equiv.refl _

@[simp, grind =] theorem of_val (x) : of (val x) = x := rfl
@[simp, grind =] theorem val_of (x) : val (of x) = x := rfl

instance : Bot Simplicity := ⟨of 0⟩

@[simp, grind =] theorem of_zero : of 0 = ⊥ := rfl
@[simp, grind =] theorem val_zero : val ⊥ = 0 := rfl

instance : FunLike Simplicity NatOrdinal SignType where
  coe x := x.val
  coe_injective' _ := by simp

@[simp, grind =] theorem val_apply (x o) : val x o = x o := rfl
@[simp, grind =] theorem of_apply (x o) : of x o = x o := rfl

@[simp, grind =] theorem coe_bot : ⇑(⊥ : Simplicity) = 0 := rfl
theorem bot_apply (o) : (⊥ : Simplicity) o = 0 := rfl

@[ext]
protected theorem ext {x y : Simplicity} (hxy : ∀ o, x o = y o) : x = y :=
  DFunLike.coe_injective (funext hxy)

/-- A recursor for `Simplicity`. Use as `cases x`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
protected def ind {motive : Simplicity → Sort*} (of : ∀ a, motive (of a)) (a) : motive a :=
  of a.val

/-! ### Order instances -/

instance : Preorder Simplicity where
  le x y := y.val ↾ x.val.length = x.val
  le_refl x := by simp
  le_trans x y z := by grind

theorem le_def {x y : Simplicity} : x ≤ y ↔ y.val ↾ x.val.length = x.val := .rfl
theorem of_le_of {x y} : of x ≤ of y ↔ y ↾ x.length = x := .rfl

theorem le_restrict_of_le_of_length_le {x y : Simplicity} {o : WithTop NatOrdinal}
    (h : x ≤ y) (h' : x.val.length ≤ o) : x ≤ of (val y ↾ o) := by
  simp_all [le_def]

theorem le_iff_forall {x y : Simplicity} : x ≤ y ↔ ∀ o, x o ≠ 0 → x o = y o := by
  refine ⟨fun h o ho ↦ ?_, fun H ↦ ?_⟩
  · rw [← val_apply, ← le_def.1 h, restrict_apply_of_coe_lt, val_apply]
    rwa [← apply_ne_zero]
  · ext o
    rw [eq_comm]
    obtain ho | ho := lt_or_ge (↑o) x.val.length
    · rw [restrict_apply_of_coe_lt ho]
      exact H _ (apply_ne_zero.2 ho)
    · rwa [restrict_apply_of_le_coe ho, apply_eq_zero]

theorem apply_eq_of_le {x y : Simplicity} {o : NatOrdinal} (h : x ≤ y) (hx : x o ≠ 0) :
    x o = y o := by
  rw [← val_apply, ← le_def.1 h, restrict_apply_of_coe_lt, val_apply]
  rwa [← apply_ne_zero]

theorem le_of_le_of_length_le {x y z : Simplicity} (hx : x ≤ z) (hy : y ≤ z)
    (h : x.val.length ≤ y.val.length) : x ≤ y := by
  rw [le_iff_forall]
  intro o ho
  rw [apply_eq_of_le hx ho, apply_eq_of_le hy]
  rw [← val_apply, apply_ne_zero] at ho ⊢
  exact ho.trans_le h

theorem le_or_ge_of_le {x y z : Simplicity} (hx : x ≤ z) (hy : y ≤ z) : x ≤ y ∨ y ≤ x := by
  obtain h | h := le_total x.val.length y.val.length
  · exact .inl <| le_of_le_of_length_le hx hy h
  · exact .inr <| le_of_le_of_length_le hy hx h

theorem of_restrict_le_of (x : SignExpansion) (o : WithTop NatOrdinal) : of (x ↾ o) ≤ of x := by
  rw [of_le_of, length_restrict, ← restrict_restrict_eq, restrict_of_length_le le_rfl]

theorem eq_or_length_lt_of_le {x y : Simplicity} (h : x ≤ y) :
    x = y ∨ x.val.length < y.val.length := by
  rw [le_def] at h
  have := lt_or_ge x.val.length y.val.length
  aesop

theorem length_strictMono : StrictMono fun x : Simplicity ↦ x.val.length :=
  fun _ _ h ↦ (eq_or_length_lt_of_le h.le).resolve_left h.ne

instance : PartialOrder Simplicity where
  le_antisymm x y h₁ h₂ := by
    have := eq_or_length_lt_of_le h₁
    have := eq_or_length_lt_of_le h₂
    grind

instance : OrderBot Simplicity where
  bot_le := by simp [le_def]

/-! ### Infimum -/

open Classical in
@[no_expose]
instance : InfSet Simplicity where
  sInf s := if hs : s.Nonempty then
    of (hs.choose.val ↾ sInf ((↑) '' {i | ∃ y ∈ s, ∃ z ∈ s, y i ≠ z i}))
  else ⊥

@[simp]
theorem sInf_empty : sInf ∅ = (⊥ : Simplicity) :=
  dif_neg (by simp)

private theorem sInf_eq_of_mem {s : Set Simplicity} {x : Simplicity} (hx : x ∈ s) :
    sInf s = of (x.val ↾ sInf ((↑) '' {i | ∃ y ∈ s, ∃ z ∈ s, y i ≠ z i})) := by
  have hs : s.Nonempty := ⟨x, hx⟩
  have hsc := hs.choose_spec
  apply (dif_pos hs).trans
  rw [of.apply_eq_iff_eq]
  ext i
  obtain ha | ha := lt_or_ge (i : WithTop NatOrdinal)
    (sInf ((↑) '' {i | ∃ y ∈ s, ∃ z ∈ s, y i ≠ z i}))
  · rw [restrict_apply_of_coe_lt ha, restrict_apply_of_coe_lt ha]
    have := notMem_of_lt_csInf' ha
    grind
  · rw [restrict_apply_of_le_coe ha, restrict_apply_of_le_coe ha]

theorem isGLB_sInf_of_nonempty {s : Set Simplicity} (hs : s.Nonempty) : IsGLB s (sInf s) := by
  constructor <;> intro x hx
  · rw [sInf_eq_of_mem hx]
    exact of_restrict_le_of ..
  · obtain ⟨y, hy⟩ := hs
    rw [sInf_eq_of_mem hy]
    apply le_restrict_of_le_of_length_le (hx hy)
    rw [le_sInf_iff]
    rintro i ⟨o, ⟨a, ha, b, hb, H⟩, rfl⟩
    contrapose! H
    rw [← apply_ne_zero] at H
    rw [← apply_eq_of_le (hx ha) H, ← apply_eq_of_le (hx hb) H]

instance : SemilatticeInf Simplicity :=
  .ofIsGLB _ fun a b ↦ isGLB_sInf_of_nonempty (by simp)

theorem sInf_pair (x y : Simplicity) : sInf {x, y} = x ⊓ y := (rfl)

instance : CompleteSemilatticeInf (WithTop Simplicity) where
  isGLB_sInf := by exact WithTop.isGLB_sInf_of_nonempty fun _ ↦ isGLB_sInf_of_nonempty

/-! ### Supremum -/

open Classical in
@[no_expose]
instance : SupSet Simplicity where
  sSup s := if IsChain (· ≤ ·) s then
    of ⟨fun i ↦ if h : ∃ x ∈ s, x i ≠ 0 then h.choose i else 0, ?_⟩ else ⊥
where finally
  intro a b h
  simp only [ne_eq, Set.mem_preimage, Set.mem_singleton_iff, dite_eq_right_iff,
    forall_exists_index, forall_and_index]
  refine fun H x hx hb ↦ isUpperSet_preimage_singleton_zero _ h ?_
  have := H x hx ?_
  · generalize_proofs H' at this
    cases H'.choose_spec.2 this
  · contrapose! hb
    exact isUpperSet_preimage_singleton_zero _ h hb

@[simp]
theorem sSup_empty : sSup ∅ = (⊥ : Simplicity) := by
  ext; simp [sSup]

private theorem sSup_apply_of_mem {x : Simplicity} {s : Set Simplicity}
    (hs : IsChain (· ≤ ·) s) (hx : x ∈ s) {o : NatOrdinal} (ho : x o ≠ 0) : sSup s o = x o := by
  dsimp [sSup]
  rw [if_pos hs, of_apply, coe_mk, dif_pos ⟨x, hx, ho⟩]
  generalize_proofs H
  obtain ⟨hc, hc'⟩ := H.choose_spec
  obtain h | h := hs.total hx hc <;> rwa [apply_eq_of_le h]

private theorem exists_of_sSup_apply_ne_zero {s : Set Simplicity} (hs : IsChain (· ≤ ·) s)
    {o : NatOrdinal} (ho : sSup s o ≠ 0) : ∃ x ∈ s, x o ≠ 0 := by
  dsimp [sSup] at ho
  aesop

private theorem isLUB_sSup_of_isChain {s : Set Simplicity} (hs : IsChain (· ≤ ·) s) :
    IsLUB s (sSup s) := by
  constructor <;> intro x hx <;> rw [le_iff_forall] <;> intro o ho
  · exact (sSup_apply_of_mem hs hx ho).symm
  · obtain ⟨y, hy, hy'⟩ := exists_of_sSup_apply_ne_zero hs ho
    rw [sSup_apply_of_mem hs hy hy', apply_eq_of_le (hx hy) hy']

theorem isChain_iff_bddAbove {s : Set Simplicity} : IsChain (· ≤ ·) s ↔ BddAbove s where
  mp hs := ⟨_, (isLUB_sSup_of_isChain hs).1⟩
  mpr hs := by
    obtain ⟨z, hz⟩ := hs
    exact fun x hx y hy _ ↦ le_or_ge_of_le (hz hx) (hz hy)

theorem isLUB_sSup_iff_bddAbove {s : Set Simplicity} : IsLUB s (sSup s) ↔ BddAbove s where
  mp hs := hs.bddAbove
  mpr hs := by
    rw [← isChain_iff_bddAbove] at hs
    exact isLUB_sSup_of_isChain hs

theorem sSup_of_not_bddAbove {s : Set Simplicity} (hs : ¬ BddAbove s) : sSup s = ⊥ := by
  apply dif_neg
  rwa [isChain_iff_bddAbove]

instance : Max Simplicity where
  max x y := sSup {x, y}

theorem sSup_pair (x y : Simplicity) : sSup {x, y} = x ⊔ y := rfl

protected theorem sup_comm (x y : Simplicity) : x ⊔ y = y ⊔ x :=
  congrArg sSup <| Set.pair_comm x y

protected theorem sup_of_le_right {x y : Simplicity} (h : x ≤ y) : x ⊔ y = y := by
  apply (isLUB_sSup_iff_bddAbove.2 ?_).unique
  · simpa [IsLUB, IsLeast, lowerBounds]
  · rw [← isChain_iff_bddAbove]
    exact .pair h

protected theorem sup_of_le_left {x y : Simplicity} (h : y ≤ x) : x ⊔ y = x := by
  rw [Simplicity.sup_comm]
  exact Simplicity.sup_of_le_right h

open Classical in
instance : CompleteSemilatticeSup (WithTop Simplicity) where
  isLUB_sSup s := by
    change IsLUB s (dite ..)
    split_ifs with h hs
    · simp [isLUB_iff_le_iff, upperBounds, WithTop.forall, h]
    · exact WithTop.isLUB_of_coe_preimage h (isLUB_sSup_iff_bddAbove.2 hs)
    · simpa [isLUB_iff_le_iff, upperBounds, WithTop.forall, h, bddAbove_def] using hs

instance : CompleteLattice (WithTop Simplicity) where
  __ := WithTop.instBoundedOrder
  __ := instCompleteSemilatticeInfWithTop
  __ := completeLatticeOfCompleteSemilatticeSup _

end Simplicity
