/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import CombinatorialGames.Surreal.Scale.OptionGaps

import Mathlib.Algebra.Group.Subgroup.Order

import CombinatorialGames.Mathlib.Subring.RescaleFactors
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import CombinatorialGames.Surreal.Omnific.Coset
import CombinatorialGames.Surreal.Omnific.Divisibility
import CombinatorialGames.Surreal.Omnific.Refinement.Integer
import Mathlib.Tactic.Linter.HaveILetI

/-!
# Making the four factors whole at a growth scale
-/

universe u

public noncomputable section

namespace Surreal

variable (C D : Subring Surreal.{u}) [C.toAddSubgroup.IsConvex]

private def scalarInclusion (h : C ≤ D) :
    residueSubfield C →+* (residueRepresentatives C ⊓ D : Subring Surreal) where
  toFun k := ⟨k, let hk := (mem_residueSubfield_iff C).mp k.2
    Subring.mem_inf.mpr ⟨hk.1, h hk.2⟩⟩
  map_zero' := Subtype.ext rfl
  map_one' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

private def scalarRetraction :
    (residueRepresentatives C ⊓ D : Subring Surreal) →+* residueSubfield C :=
  let r := (residueRetraction C C le_rfl).comp (Subring.inclusion inf_le_left :
    (residueRepresentatives C ⊓ D : Subring Surreal) →+* residueRepresentatives C)
  let val := fun z : (residueRepresentatives C ⊓ C : Subring Surreal) ↦ (z : Surreal)
  { toFun x := ⟨r x, (mem_residueSubfield_iff C).mpr (Subring.mem_inf.mp (r x).2)⟩
    map_zero' := Subtype.ext (congrArg val r.map_zero)
    map_one' := Subtype.ext (congrArg val r.map_one)
    map_add' x y := Subtype.ext (congrArg val (r.map_add x y))
    map_mul' x y := Subtype.ext (congrArg val (r.map_mul x y)) }

private theorem scalarRetraction_apply (x : (residueRepresentatives C ⊓ D : Subring Surreal)) :
    (scalarRetraction C D x : Surreal) = (x : Surreal) - cosetRep C.toAddSubgroup x := by
  change ((residueRetraction C C le_rfl (Subring.inclusion inf_le_left x)) : Surreal) = _
  rw [coe_residueRetraction, Subring.coe_inclusion]

private def scalarAlgRetraction (h : C ≤ D) :
    letI := (scalarInclusion C D h).toAlgebra
    (residueRepresentatives C ⊓ D : Subring Surreal) →ₐ[residueSubfield C] residueSubfield C := by
  letI := (scalarInclusion C D h).toAlgebra
  refine { toRingHom := scalarRetraction C D, commutes' := fun x ↦ ?_ }
  apply Subtype.ext
  rw [Algebra.algebraMap_self, RingHom.id_apply]
  change (scalarRetraction C D (scalarInclusion C D h x) : Surreal) = (x : Surreal)
  rw [scalarRetraction_apply]
  change (x : Surreal) - cosetRep C.toAddSubgroup x = (x : Surreal)
  rw [cosetRep_eq_zero_iff.mpr ((mem_residueSubfield_iff C).mp x.2).2, sub_zero]

private def wholeScalars : Subring (residueSubfield C) :=
  omnific.comap (residueSubfield C).subtype

private def wholeScalarEquiv : wholeScalars C ≃+* (omnific ⊓ C : Subring Surreal) where
  toFun x := ⟨x.1, Subring.mem_inf.mpr ⟨x.2, ((mem_residueSubfield_iff C).mp x.1.2).2⟩⟩
  invFun x := ⟨⟨x, (mem_residueSubfield_iff C).mpr
    ⟨omnific_le_residueRepresentatives C (Subring.mem_inf.mp x.2).1,
      (Subring.mem_inf.mp x.2).2⟩⟩, (Subring.mem_inf.mp x.2).1⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

private theorem mem_wholeScalars_scalarRetraction_iff
    (x : (residueRepresentatives C ⊓ D : Subring Surreal)) :
    scalarRetraction C D x ∈ wholeScalars C ↔ IsOmnific (x : Surreal) := by
  change (scalarRetraction C D x : Surreal) ∈ omnific ↔ _
  rw [mem_omnific_iff, scalarRetraction_apply]
  simpa only [coe_residueRetraction, Subring.coe_inclusion] using
    (isOmnific_iff_isOmnific_residueRetraction C C le_rfl
      (Subring.inclusion inf_le_left x)).symm

private theorem mem_of_whole_mul_mem [D.toAddSubgroup.IsConvex] {x y : Surreal.{u}}
    (hxy : x * y ∈ D) (hy : IsOmnific y) (hy₀ : y ≠ 0) : x ∈ D := by
  have habs : IsOmnific |y| := mem_omnific_iff.mp (abs_mem_iff.mpr (mem_omnific_iff.mpr hy))
  have hle : |x| ≤ |x * y| := by
    rw [abs_mul]
    exact le_mul_of_one_le_right (abs_nonneg _) (habs.one_le_iff_pos.mpr (abs_pos.mpr hy₀))
  exact abs_mem_iff.mp
    (D.toAddSubgroup.mem_of_nonneg_of_le (abs_nonneg _) hle (abs_mem_iff.mpr hxy))

private theorem rescale_zero_row [D.toAddSubgroup.IsConvex]
    (p q : Fin 2 → (residueRepresentatives C ⊓ D : Subring Surreal))
    (hz : ∀ j, scalarRetraction C D (q j) = 0) :
    ∃ u v : Fin 2 → (omnific ⊓ D : Subring Surreal),
      ∀ i j, (u i : Surreal) * v j = (p i : Surreal) * q j := by
  classical
  by_cases hn : ∃ i j, (p i : Surreal) * q j ≠ 0
  · obtain ⟨i₀, j₀, h₀⟩ := hn
    have fix (j) : cosetRep C.toAddSubgroup (q j) = q j := by
      have h := congrArg Subtype.val (hz j)
      change (scalarRetraction C D (q j) : Surreal) = 0 at h
      rw [scalarRetraction_apply, sub_eq_zero] at h
      exact h.symm
    obtain ⟨t, hp, hq⟩ := exists_wpow_rescaling_of_cosetReps C
      (fun i : Fin 2 ↦ (p i : Surreal)) (fun j : Fin 2 ↦ (q j : Surreal))
      (fun i ↦ (Subring.mem_inf.mp (p i).2).1) fix
    let u (i) := ω^ t * (p i : Surreal)
    let v (j) := (q j : Surreal) / ω^ t
    have hu (i) : IsOmnific (u i) := isOmnific_of_cosetRep_eq (hp i)
    have hv (j) : IsOmnific (v j) := isOmnific_of_cosetRep_eq (hq j)
    have prod (i j) : u i * v j = (p i : Surreal) * q j := by
      dsimp only [u, v]
      field_simp [wpow_ne_zero]
    have bound (i j) : u i * v j ∈ D :=
      prod i j ▸ D.mul_mem (Subring.mem_inf.mp (p i).2).2 (Subring.mem_inf.mp (q j).2).2
    have huv : u i₀ * v j₀ ≠ 0 := prod i₀ j₀ ▸ h₀
    refine ⟨fun i ↦ ⟨u i, Subring.mem_inf.mpr ⟨mem_omnific_iff.mpr (hu i), ?_⟩⟩,
      fun j ↦ ⟨v j, Subring.mem_inf.mpr ⟨mem_omnific_iff.mpr (hv j), ?_⟩⟩, prod⟩
    · exact mem_of_whole_mul_mem D (bound i j₀) (hv j₀) (right_ne_zero_of_mul huv)
    · exact mem_of_whole_mul_mem D (mul_comm (u i₀) (v j) ▸ bound i₀ j) (hu i₀)
        (left_ne_zero_of_mul huv)
  · push Not at hn
    exact ⟨0, 0, fun i j ↦ by
      simpa only [Pi.zero_apply, Subring.coe_zero, mul_zero] using (hn i j).symm⟩

/-- A refinement of four bounded whole entries by representatives can be rescaled to a whole
refinement as soon as the lower residue of the first entry is an ordinary integer. -/
theorem whole_refinement_at_scale [D.toAddSubgroup.IsConvex] (hle : C ≤ D)
    {a b c d : (omnific ⊓ D : Subring Surreal.{u})}
    (hres : ∃ n : ℤ, (n : Surreal) = (a : Surreal) - cosetRep C.toAddSubgroup a)
    {e f g h : (residueRepresentatives C ⊓ D : Subring Surreal)}
    (ha : (a : Surreal) = e * (f : Surreal)) (hb : (b : Surreal) = g * (h : Surreal))
    (hc : (c : Surreal) = e * (g : Surreal)) (hd : (d : Surreal) = f * (h : Surreal)) :
    ∃ e f g h : (omnific ⊓ D : Subring Surreal), a = e * f ∧ b = g * h ∧ c = e * g ∧ d = f * h := by
  classical
  let R := residueRepresentatives C ⊓ D
  let W := omnific ⊓ D
  let S := wholeScalars C
  let := (scalarInclusion C D hle).toAlgebra
  let π := scalarAlgRetraction C D hle
  let p : Fin 2 → R := ![e, h]
  let q : Fin 2 → R := ![f, g]
  let m : Fin 2 → Fin 2 → W := ![![a, c], ![d, b]]
  have eqn (i j : Fin 2) : (m i j : Surreal) = (p i : Surreal) * (q j : Surreal) := by
    fin_cases i <;> fin_cases j
    exacts [ha, hc, hd.trans (mul_comm _ _), hb.trans (mul_comm _ _)]
  have finish (u v : Fin 2 → W) (entry : ∀ i j, m i j = u i * v j) :
      ∃ e f g h : W, a = e * f ∧ b = g * h ∧ c = e * g ∧ d = f * h :=
    ⟨_, _, _, _, entry 0 0, (entry 1 1).trans (mul_comm _ _), entry 0 1,
      (entry 1 0).trans (mul_comm _ _)⟩
  by_cases hp : ∃ i, π (p i) ≠ 0
  case neg =>
    push Not at hp
    obtain ⟨v, u, heq⟩ := rescale_zero_row C D q p hp
    exact finish u v fun i j ↦ Subtype.ext (by
      rw [eqn, mul_comm, ← heq, Subring.coe_mul, mul_comm])
  by_cases hq : ∃ j, π (q j) ≠ 0
  case neg =>
    push Not at hq
    obtain ⟨u, v, heq⟩ := rescale_zero_row C D p q hq
    exact finish u v fun i j ↦ Subtype.ext ((eqn i j).trans (heq i j).symm)
  have whole (i j) : π (p i * q j) ∈ S := by
    apply (mem_wholeScalars_scalarRetraction_iff C D _).mpr
    rw [Subring.coe_mul, ← eqn i j]
    exact mem_omnific_iff.mp (Subring.mem_inf.mp (m i j).2).1
  have hpr : IsPrimal (⟨π (p 0 * q 0), whole 0 0⟩ : S) := by
    obtain ⟨n, hn⟩ := hres
    have heq : (⟨π (p 0 * q 0), whole 0 0⟩ : S) = (n : S) := by
      apply Subtype.ext
      apply Subtype.ext
      change (scalarRetraction C D (p 0 * q 0) : Surreal) = (n : Surreal)
      rwa [scalarRetraction_apply, Subring.coe_mul, ← eqn 0 0, eq_comm]
    rw [heq]
    apply ((wholeScalarEquiv C).isPrimal_iff _).mp
    rw [map_intCast]
    apply (isPrimal_inclusion_omnific_iff C _).mp
    rw [map_intCast]
    exact isPrimal_omnific_intCast n
  obtain ⟨u, v, hu, hv, huv⟩ :=
    Subring.rescale_nonzero_four_factors S π p q hp hq whole hpr
  let toWhole (x : R) (hx : π x ∈ S) : W := ⟨x, Subring.mem_inf.mpr
    ⟨mem_omnific_iff.mpr ((mem_wholeScalars_scalarRetraction_iff C D x).mp hx),
      (Subring.mem_inf.mp x.2).2⟩⟩
  exact finish (fun i ↦ toWhole (u i) (hu i)) (fun j ↦ toWhole (v j) (hv j))
    fun i j ↦ Subtype.ext ((eqn i j).trans (congrArg Subtype.val (huv i j)).symm)

end Surreal
