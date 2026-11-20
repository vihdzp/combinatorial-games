/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import CombinatorialGames.Surreal.Scale.Rounding
public import CombinatorialGames.Surreal.Scale.Bounded.Precision

/-!
# Representatives bounded by powers of a growth monomial

The residue representatives in the upper growth subring form an algebra over the residue
subfield for the corresponding lower growth ring. Rounding at nonnegative precisions
preserves the upper growth bound.
-/

universe u

public noncomputable section

namespace Surreal

variable (i : Surreal.{u})

local notation "C" => lowerGrowthSubring i
local notation "U" => residueRepresentatives (lowerGrowthSubring i)
local notation "K" => residueSubfield (lowerGrowthSubring i)
local notation "A" => unitExponentSubgroup (lowerGrowthSubring i)

private theorem div_wpow_mem_upperGrowthSubring {t x : Surreal.{u}} (ht : 0 ≤ t)
    (hx : x ∈ upperGrowthSubring i) : x / ω^ t ∈ upperGrowthSubring i := by
  obtain ⟨n, hn⟩ := (mem_upperGrowthSubring_iff i).mp hx
  refine (mem_upperGrowthSubring_iff i).mpr ⟨n, ?_⟩
  have hm : 1 ≤ ω^ t := by simpa only [wpow_zero] using wpow_le_wpow.mpr ht
  rw [abs_div, abs_of_pos (wpow_pos t)]
  exact (div_le_self (abs_nonneg x) hm).trans hn

/-- The residue representatives belonging to the upper growth subring. -/
abbrev boundedResidueRepresentatives : Subring Surreal.{u} :=
  U ⊓ upperGrowthSubring i

local notation "V" => boundedResidueRepresentatives i

/-- A bounded residue representative lies in both the representative ring and the upper
growth subring. -/
theorem mem_boundedResidueRepresentatives {x : Surreal.{u}} :
    x ∈ V ↔ x ∈ U ∧ x ∈ upperGrowthSubring i := Subring.mem_inf

/-- Inclusion of the residue subfield for the lower growth ring into the bounded
representatives. -/
def boundedResidueAlgebraMap : K →+* V where
  toFun k := ⟨k, (mem_boundedResidueRepresentatives i).mpr
    ⟨((mem_residueSubfield_iff C).mp k.2).1,
      lowerGrowthSubring_le_upperGrowthSubring i ((mem_residueSubfield_iff C).mp k.2).2⟩⟩
  map_zero' := Subtype.ext rfl
  map_one' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

instance boundedResidueAlgebra : Algebra K V :=
  (boundedResidueAlgebraMap i).toAlgebra

/-- Scalars in the bounded representative algebra have their original surreal values. -/
theorem coe_boundedResidue_algebraMap (k : K) :
    ((algebraMap K V k : V) : Surreal.{u}) = k := (rfl)

/-- Nonnegative rounding preserves the upper growth bound of a residue representative. -/
theorem roundAt_mem_boundedResidueRepresentatives {t : Surreal.{u}} (ht : 0 ≤ t) (x : V) :
    roundAt C t x ∈ V := by
  refine (mem_boundedResidueRepresentatives i).mpr
    ⟨roundAt_mem_residueRepresentatives C t x, ?_⟩
  have hx := div_wpow_mem_upperGrowthSubring i ht ((mem_boundedResidueRepresentatives i).mp x.2).2
  have he : (x : Surreal.{u}) / ω^ t - roundAt C t x ∈ lowerGrowthSubring i := by
    rw [roundAt_eq]
    exact infinitesimals_le C (sub_cosetRep_mem _ _)
  simpa only [sub_sub_cancel] using
    (upperGrowthSubring i).sub_mem hx (lowerGrowthSubring_le_upperGrowthSubring i he)

/-- Rounding at a nonnegative precision, evaluated in the bounded representative ring. -/
def boundedRound {t : Surreal.{u}} (ht : 0 ≤ t) (x : V) : V :=
  ⟨roundAt C t x, roundAt_mem_boundedResidueRepresentatives i ht x⟩

/-- The underlying surreal of a bounded rounding. -/
theorem coe_boundedRound {t : Surreal.{u}} (ht : 0 ≤ t) (x : V) :
    (boundedRound i ht x : Surreal.{u}) = roundAt C t x := (rfl)

/-- Bounded rounding at zero is the identity. -/
@[simp] theorem boundedRound_zero (x : V) :
    boundedRound i (le_rfl : (0 : Surreal.{u}) ≤ 0) x = x := by
  apply Subtype.ext
  rw [coe_boundedRound, roundAt_zero_precision]
  exact (mem_residueRepresentatives_iff C).mp ((mem_boundedResidueRepresentatives i).mp x.2).1

/-- Bounded rounding at a fixed precision is additive. -/
def boundedRoundHom {t : Surreal.{u}} (ht : 0 ≤ t) : V →+ V where
  toFun := boundedRound i ht
  map_zero' := Subtype.ext (by simp [coe_boundedRound, roundAt_eq])
  map_add' x y := Subtype.ext (by
    simpa only [coe_boundedRound, Subring.coe_add] using roundAt_add C t x y)

theorem boundedRoundHom_apply {t : Surreal.{u}} (ht : 0 ≤ t) (x : V) :
    boundedRoundHom i ht x = boundedRound i ht x := (rfl)

/-- Rounding twice at nonnegative precisions adds the two precisions. -/
theorem boundedRound_boundedRound {s t : Surreal.{u}} (hs : 0 ≤ s) (ht : 0 ≤ t) (x : V) :
    boundedRound i ht (boundedRound i hs x) = boundedRound i (add_nonneg hs ht) x := by
  apply Subtype.ext
  simp only [coe_boundedRound, roundAt_roundAt C s ht]

/-- The Conway monomial of a bounded precision belongs to the bounded representative ring. -/
theorem wpow_mem_boundedResidueRepresentatives {t : Surreal.{u}} (ht : t ∈ boundedPrecision i) :
    ω^ t ∈ V := by
  obtain ⟨ht₀, _, n, hn⟩ := (mem_boundedPrecision i).mp ht
  apply (mem_boundedResidueRepresentatives i).mpr
  refine ⟨?_, (mem_upperGrowthSubring_iff i).mpr ⟨n, ?_⟩⟩
  · simpa only [mul_one] using wpow_mul_mem_residueRepresentatives C ht₀ (U).one_mem
  · rwa [abs_of_pos (wpow_pos t), growthMonomial_eq, ← wpow_natCast_mul, wpow_le_wpow]

/-- The monomial corresponding to a bounded precision, evaluated in the bounded ring. -/
def boundedMonomial {t : Surreal.{u}} (ht : t ∈ boundedPrecision i) : V :=
  ⟨ω^ t, wpow_mem_boundedResidueRepresentatives i ht⟩

/-- The underlying surreal of a bounded monomial. -/
theorem coe_boundedMonomial {t : Surreal.{u}} (ht : t ∈ boundedPrecision i) :
    (boundedMonomial i ht : Surreal.{u}) = ω^ t := (rfl)

private theorem cosetRep_natCast_mul_growthExponent_eq (n : ℕ) :
    cosetRep A ((n : Surreal.{u}) * ω^ i) = (n : Surreal.{u}) * ω^ i := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Nat.cast_succ, add_mul, one_mul, cosetRep_add, ih, cosetRep_growthExponent_eq]

/-- The precision level of a nonzero bounded representative is bounded. -/
theorem precisionLevel_mem_boundedPrecision (x : V) (hx : x ≠ 0) :
    precisionLevel C (x : Surreal.{u}) ∈ boundedPrecision i := by
  have hx₀ : (x : Surreal.{u}) ≠ 0 := fun e ↦ hx (Subtype.ext e)
  have hupper := ((mem_boundedResidueRepresentatives i).mp x.2).2
  have hm : ω^ ((x : Surreal.{u}).wlog) ∈ upperGrowthSubring i :=
    (mem_subring_iff_of_veq (upperGrowthSubring i) (wpow_wlog_veq hx₀)).mpr hupper
  obtain ⟨n, hn⟩ := (mem_upperGrowthSubring_iff i).mp hm
  have hlevel : (x : Surreal.{u}).wlog ≤ (n : Surreal.{u}) * ω^ i := by
    rwa [abs_of_pos (wpow_pos _), growthMonomial_eq, ← wpow_natCast_mul, wpow_le_wpow] at hn
  refine (mem_boundedPrecision i).mpr
    ⟨precisionLevel_nonneg_of_mem_residueRepresentatives C
      ((mem_boundedResidueRepresentatives i).mp x.2).1 hx₀, cosetRep_precisionLevel C x,
      n, ?_⟩
  have he := monotone_cosetRep A hlevel
  rw [cosetRep_natCast_mul_growthExponent_eq] at he
  simpa only [precisionLevel_eq] using he

/-- A precision strictly beyond the nonzero representative's level reads zero. -/
theorem boundedRound_eq_zero_of_level_lt {t : Surreal.{u}} (ht : 0 ≤ t)
    (htfix : cosetRep A t = t) (x : V)
    (hlt : precisionLevel C (x : Surreal.{u}) < t) : boundedRound i ht x = 0 := by
  apply Subtype.ext
  rw [coe_boundedRound, roundAt_eq]
  by_cases hx : (x : Surreal.{u}) = 0
  · rw [hx, zero_div, cosetRep_zero]
    rfl
  · exact cosetRep_eq_zero_iff.mpr ((div_wpow_mem_infinitesimals_iff C hx htfix).mpr hlt)

/-- Every positive bounded reading discards the constant one. -/
theorem boundedRoundHom_one_of_pos {t : Surreal.{u}} (ht : t ∈ boundedPrecision i) (hp : 0 < t) :
    boundedRoundHom i hp.le 1 = 0 := by
  rw [boundedRoundHom_apply]
  apply boundedRound_eq_zero_of_level_lt i hp.le ((mem_boundedPrecision i).mp ht).2.1
  change precisionLevel C 1 < t
  simpa only [← wpow_zero, precisionLevel_wpow, cosetRep_zero] using hp

end Surreal
