/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import CombinatorialGames.Mathlib.FourFactorRefinement
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Algebra.Order.Monoid.Submonoid

import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Tactic.TypeStar

/-!
# Generating rows in ordered group algebras

The supports of one point generate a finite lattice. Its line equation holds separately
on each coset, so a row chosen in the lattice generates every point over the entire group.
Shift by the smaller of the two least row exponents to descend to the nonnegative cone.
-/

public noncomputable section

namespace AddMonoidAlgebra

variable {R G H : Type*} [CommRing R] [AddCommGroup G] [AddCommMonoid H]

/-- A finite sum comes from a submonoid precisely when its exponents do. -/
theorem mem_range_mapDomainRingHom_iff (f : H →+ G) (hf : Function.Injective f)
    (p : AddMonoidAlgebra R G) :
    p ∈ Set.range (mapDomainRingHom R f) ↔ ∀ g ∈ p.coeff.support, g ∈ Set.range f := by
  constructor
  · rintro ⟨q, rfl⟩ g hg
    by_contra hn
    apply Finsupp.mem_support_iff.mp hg
    rw [mapDomainRingHom_apply]
    change Finsupp.mapDomain f q.coeff g = 0
    exact Finsupp.mapDomain_of_notMem_range q.coeff g hn
  · intro h
    exact ⟨comapDomain f hf p, by
      rw [mapDomainRingHom_apply]
      exact mapDomain_comapDomain h hf⟩

end AddMonoidAlgebra

namespace AddMonoidAlgebra
variable {R G : Type*} [CommRing R] [AddCommGroup G] (U : AddSubgroup G)
local notation "ι" => mapDomainRingHom R U.subtype

private def cosetMap (r : G) (g : U) : G := (g : G) + r

private theorem cosetMap_inj (r : G) : Function.Injective (cosetMap U r) :=
  fun _ _ h ↦ Subtype.ext (add_right_cancel h)

private abbrev part (r : G) (x : AddMonoidAlgebra R G) :=
  comapDomain (cosetMap U r) (cosetMap_inj U r) x

private theorem part_mul (r : G) (a : AddMonoidAlgebra R U) (x : AddMonoidAlgebra R G) :
    part U r (ι a * x) = a * part U r x := by
  induction a using induction_linear with
  | zero => simp [part]
  | add a b ha hb => simp only [map_add, add_mul, part, comapDomain_add] at *; rw [ha, hb]
  | single g k =>
    induction x using induction_linear with
    | zero => simp [part]
    | add x y hx hy => simp only [mul_add, part, comapDomain_add] at *; rw [hx, hy]
    | single v l =>
      change part U r (mapDomain U.subtype (single g k) * single v l) = _
      rw [mapDomain_single, single_mul_single]
      by_cases hv : v ∈ Set.range (cosetMap U r)
      · obtain ⟨w, rfl⟩ := hv
        rw [show U.subtype g + cosetMap U r w = cosetMap U r (g + w) by
          simp [cosetMap, add_assoc], part, part, comapDomain_single_map, comapDomain_single_map,
          single_mul_single]
      · have hn : U.subtype g + v ∉ Set.range (cosetMap U r) := by
          rintro ⟨w, he⟩
          apply hv
          refine ⟨w - g, ?_⟩
          change (w : G) - (g : G) + r = v
          change (w : G) + r = (g : G) + v at he
          rw [show (w : G) - (g : G) + r = (w + r : G) - g by abel, he]
          abel
        rw [part, part, comapDomain_single_of_notMem_range hn,
          comapDomain_single_of_notMem_range hv, mul_zero]

open scoped Classical in
private theorem lift_part_coeff (r g : G) (x : AddMonoidAlgebra R G) :
    (single r 1 * ι (part U r x)).coeff g =
      if QuotientAddGroup.mk' U g = QuotientAddGroup.mk' U r then x.coeff g else 0 := by
  classical
  rw [coeff_single_mul_apply, one_mul]
  change (Finsupp.mapDomain U.subtype (part U r x).coeff) (-r + g) = _
  by_cases h : QuotientAddGroup.mk' U g = QuotientAddGroup.mk' U r
  · simp only [h, ↓reduceIte]
    have d : -r + g ∈ U := by
      apply (QuotientAddGroup.eq_zero_iff _).mp
      change (QuotientAddGroup.mk' U) (-r + g) = 0
      rw [map_add, map_neg, h, neg_add_cancel]
    let u : U := ⟨-r + g, d⟩
    change (Finsupp.mapDomain U.subtype (part U r x).coeff) (U.subtype u) = _
    rw [Finsupp.mapDomain_apply_of_injective (f := U.subtype) Subtype.val_injective]
    change x.coeff ((-r + g) + r) = _
    simp [add_comm]
  · simp only [h, ↓reduceIte]
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨u, hu⟩
    apply h
    have hu' : -r + g ∈ U := hu ▸ u.2
    have he : (QuotientAddGroup.mk' U) (-r + g) = 0 := (QuotientAddGroup.eq_zero_iff _).mpr hu'
    rw [map_add, map_neg] at he
    let π := QuotientAddGroup.mk' U
    calc π g = π r + (-π r + π g) := by simp
         _ = _ := by rw [he, add_zero]

/-- An equation with coefficients in a subgroup holds on each coset separately. -/
theorem row_on_cosets {a c f g : AddMonoidAlgebra R U}
    (row : ∀ x y, c * x = a * y → ∃ q, x = q * f ∧ y = q * g)
    {x y : AddMonoidAlgebra R G} (h : ι c * x = ι a * y) :
    ∃ q, x = q * ι f ∧ y = q * ι g := by
  classical
  let π := QuotientAddGroup.mk' U
  let S := (x.coeff.support ∪ y.coeff.support).image π
  have decomp (w : AddMonoidAlgebra R G)
      (hw : w.coeff.support ⊆ x.coeff.support ∪ y.coeff.support) :
      w = ∑ t ∈ S, single t.out 1 * ι (part U t.out w) := by
    ext u
    simp only [coeff_sum, Finsupp.finsetSum_apply, lift_part_coeff]
    have out (t : G ⧸ U) : π t.out = t := Quotient.out_eq t
    change w.coeff u = ∑ t ∈ S, if π u = π t.out then w.coeff u else 0
    simp_rw [out]
    by_cases hu : w.coeff u = 0
    · simp [hu]
    · simp [S, Finset.mem_image_of_mem π (hw (Finsupp.mem_support_iff.mpr hu))]
  have localRow (t : G ⧸ U) := row (part U t.out x) (part U t.out y)
    (show c * part U t.out x = a * part U t.out y by rw [← part_mul, ← part_mul, h])
  choose q hx hy using localRow
  refine ⟨∑ t ∈ S, single t.out 1 * ι (q t), ?_, ?_⟩
  · conv_lhs => rw [decomp x Finset.subset_union_left]
    simp only [hx, map_mul, Finset.sum_mul, mul_assoc]
  · conv_lhs => rw [decomp y Finset.subset_union_right]
    simp only [hy, map_mul, Finset.sum_mul, mul_assoc]

end AddMonoidAlgebra

namespace AddMonoidAlgebra
variable {R U G : Type*} [CommRing R] [AddCommGroup U] [AddCommGroup G]
variable {n : ℕ} (coord : U ≃+ (Fin n → ℤ))

/-- Include natural polynomial exponents among integer lattice coordinates. -/
def natCoordinates (n : ℕ) : (Fin n →₀ ℕ) →+ (Fin n → ℤ) where
  toFun v j := v j
  map_zero' := rfl
  map_add' v w := funext fun j ↦ Nat.cast_add (v j) (w j)

/-- The nonnegative orthant in a lattice basis. -/
abbrev fromOrthant := coord.symm.toAddMonoidHom.comp (natCoordinates n)

/-- Distinct nonnegative coordinates give distinct lattice elements. -/
theorem fromOrthant_inj : Function.Injective (fromOrthant coord) :=
  coord.symm.injective.comp fun _ _ h ↦ Finsupp.ext fun j ↦ Int.ofNat_inj.mp (congrFun h j)

/-- Evaluate the nonnegative integer coordinates in a lattice basis. -/
abbrev toLattice := mapDomainRingHom R (fromOrthant coord)

/-- One lattice translation makes every coordinate in a finite support nonnegative. -/
theorem translated_support (S : Finset U) :
    ∃ s : U, ∀ x : AddMonoidAlgebra R U, x.coeff.support ⊆ S →
      ∃ P : MvPolynomial (Fin n) R, toLattice (R := R) coord P = single (-s) 1 * x := by
  classical
  choose lo hlo using fun j : Fin n ↦ (Set.finite_range (fun g : S ↦ coord g j)).bddBelow
  refine ⟨coord.symm lo, fun x hx ↦ ?_⟩
  apply (mem_range_mapDomainRingHom_iff _ (fromOrthant_inj coord) _).mpr
  intro t ht
  obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp (support_coeff_single_mul_subset x 1 _ ht)
  have hle (j) : lo j ≤ coord g j := hlo j ⟨⟨g, hx hg⟩, rfl⟩
  let p := Finsupp.equivFunOnFinite.symm (fun j ↦ (coord g j - lo j).toNat)
  have atCoord : natCoordinates n p = coord g - lo := funext fun j ↦
    Int.toNat_of_nonneg (sub_nonneg.mpr (hle j))
  refine ⟨p, ?_⟩
  change coord.symm (natCoordinates n p) = _
  rw [atCoord, map_sub, coord.symm_apply_apply]
  exact sub_eq_neg_add ..

include coord in
private theorem rows_on_lattice (solve : HasGeneratingRows (MvPolynomial (Fin n) R)) :
    HasGeneratingRows (AddMonoidAlgebra R U) := by
  classical
  intro a c ha
  let φ := toLattice (R := R) coord
  have inj : Function.Injective φ := mapDomain_injective (fromOrthant_inj coord)
  let m (s : U) : AddMonoidAlgebra R U := single s 1
  have cancel (s : U) (x : AddMonoidAlgebra R U) : m s * (m (-s) * x) = x := by
    simp [m, ← mul_assoc, single_mul_single, ← one_def]
  obtain ⟨s, lift⟩ := translated_support (R := R) coord (a.coeff.support ∪ c.coeff.support)
  obtain ⟨A, hA⟩ := lift a Finset.subset_union_left
  obtain ⟨C, hC⟩ := lift c Finset.subset_union_right
  have hn : A ≠ 0 := fun h ↦ ha (by rw [← cancel s a, ← hA, h, map_zero, mul_zero])
  obtain ⟨f, g, hf, row⟩ := solve A C hn
  refine ⟨φ f, φ g, (map_ne_zero_iff _ inj).mpr hf, fun x y hxy ↦ ?_⟩
  obtain ⟨t, lift'⟩ := translated_support (R := R) coord (x.coeff.support ∪ y.coeff.support)
  obtain ⟨X, hX⟩ := lift' x Finset.subset_union_left
  obtain ⟨Y, hY⟩ := lift' y Finset.subset_union_right
  have eqn : C * X = A * Y := inj (show φ (C * X) = φ (A * Y) by
    simp only [map_mul, φ, hA, hC, hX, hY]
    rw [mul_mul_mul_comm _ c, mul_mul_mul_comm _ a, hxy])
  obtain ⟨q, hx, hy⟩ := row X Y eqn
  have undo {w : AddMonoidAlgebra R U} {Z F : MvPolynomial (Fin n) R}
      (hZ : φ Z = m (-t) * w) (he : Z = q * F) : w = (m t * φ q) * φ F := by
    rw [mul_assoc, ← map_mul, ← he, hZ, cancel]
  exact ⟨m t * φ q, undo hX hx, undo hY hy⟩

/-- The subgroup generated by finitely many exponents has integer lattice coordinates. -/
theorem exists_lattice_coordinates [LinearOrder G] [IsOrderedAddMonoid G] (S : Finset G) :
    ∃ n, Nonempty (AddSubgroup.closure (S : Set G) ≃+ (Fin n → ℤ)) := by
  let H := AddSubgroup.closure (S : Set G)
  have hh : H.toIntSubmodule = Submodule.span ℤ (S : Set G) := AddSubgroup.toIntSubmodule_closure _
  have : Module.Finite ℤ H := Module.Finite.iff_fg (N := H.toIntSubmodule).mpr
    (hh ▸ Submodule.fg_span S.finite_toSet)
  obtain ⟨n, basis⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := H)
  exact ⟨n, ⟨basis.equivFun.toAddEquiv⟩⟩

/-- One row chosen in the lattice of a and c still serves every coset of that lattice. -/
theorem generating_rows_group [LinearOrder G] [IsOrderedAddMonoid G]
    (solve : ∀ n, HasGeneratingRows (MvPolynomial (Fin n) R)) :
    HasGeneratingRows (AddMonoidAlgebra R G) := by
  classical
  intro a c ha
  let S := a.coeff.support ∪ c.coeff.support
  let H := AddSubgroup.closure (S : Set G)
  obtain ⟨n, ⟨coord⟩⟩ := exists_lattice_coordinates S
  let φ := mapDomainRingHom R H.subtype
  have lift (x : AddMonoidAlgebra R G) (hx : x.coeff.support ⊆ S) : x ∈ Set.range φ := by
    apply (mem_range_mapDomainRingHom_iff _ Subtype.val_injective _).mpr
    exact fun k hk ↦ ⟨⟨k, AddSubgroup.subset_closure (hx hk)⟩, rfl⟩
  obtain ⟨A, hA⟩ := lift a Finset.subset_union_left
  obtain ⟨C, hC⟩ := lift c Finset.subset_union_right
  have hn : A ≠ 0 := fun h ↦ ha (hA.symm.trans (by rw [h, map_zero]))
  obtain ⟨f, g, hf, row⟩ := rows_on_lattice coord (solve n) A C hn
  exact ⟨φ f, φ g, (map_ne_zero_iff _ (mapDomain_injective Subtype.val_injective)).mpr hf,
    fun x y h ↦ row_on_cosets H row (hA ▸ hC ▸ h)⟩

end AddMonoidAlgebra

namespace AddMonoidAlgebra
variable {R G : Type*} [CommRing R] [IsDomain R] [AddCommGroup G] [LinearOrder G]
  [IsOrderedAddMonoid G]
/-- Include the nonnegative exponents in the group ring. -/
abbrev coneMap :=
  mapDomainRingHom R (AddSubmonoid.nonneg G).subtype

omit [IsDomain R] in
/-- A group-ring element lies in the cone precisely when all its exponents are nonnegative. -/
theorem mem_range_coneMap (p : AddMonoidAlgebra R G) :
    p ∈ Set.range (coneMap (R := R) (G := G)) ↔ ∀ g ∈ p.coeff.support, 0 ≤ g := by
  rw [mem_range_mapDomainRingHom_iff _ Subtype.val_injective]
  simp

/-- The least exponent in a nonzero finite sum. -/
abbrev leastExp (p : AddMonoidAlgebra R G) (hp : p ≠ 0) : G :=
  p.coeff.support.min' (Finsupp.support_nonempty_iff.mpr (coeff_eq_zero.not.mpr hp))

/-- The two least exponents contribute a nonzero term to the product. -/
theorem leastExp_add_mem {p q : AddMonoidAlgebra R G} (hp : p ≠ 0) (hq : q ≠ 0) :
    leastExp p hp + leastExp q hq ∈ (p * q).coeff.support := by
  classical
  have unique : UniqueAdd p.coeff.support q.coeff.support (leastExp p hp) (leastExp q hq) := by
    intro a b ha hb he
    have h₁ : leastExp p hp ≤ a := Finset.min'_le _ _ ha
    have h₂ : leastExp q hq ≤ b := Finset.min'_le _ _ hb
    have ea : a = leastExp p hp := le_antisymm (le_of_not_gt fun hl ↦
      (add_lt_add_of_lt_of_le hl h₂).ne he.symm) h₁
    exact ⟨ea, add_left_cancel (ea ▸ he)⟩
  apply Finsupp.mem_support_iff.mpr
  rw [coeff_mul_add_of_uniqueAdd unique]
  exact mul_ne_zero (Finsupp.mem_support_iff.mp (Finset.min'_mem _ _))
    (Finsupp.mem_support_iff.mp (Finset.min'_mem _ _))

omit [IsDomain R] in
/-- A shifted finite sum is in the cone as soon as its least exponent is nonnegative. -/
theorem monomial_shift_mem {p : AddMonoidAlgebra R G} (hp : p ≠ 0) {g : G}
    (hg : 0 ≤ g + leastExp p hp) : single g 1 * p ∈ Set.range (coneMap (R := R)) := by
  classical
  apply (mem_range_coneMap _).2
  intro t ht
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (support_coeff_single_mul_subset p 1 g ht)
  exact hg.trans (add_le_add_right (Finset.min'_le _ _ hj) _)


/-- Shift the common row until one of its two least exponents is zero. -/
theorem generating_rows_nonneg (solve : ∀ n, HasGeneratingRows (MvPolynomial (Fin n) R)) :
    HasGeneratingRows (AddMonoidAlgebra R (AddSubmonoid.nonneg G)) := by
  classical
  intro a c ha
  by_cases hc : c = 0
  · subst c
    refine ⟨1, 0, one_ne_zero, fun x y h ↦ ⟨x, (mul_one _).symm, ?_⟩⟩
    rw [mul_zero]
    exact (mul_eq_zero.mp ((zero_mul x).symm.trans h).symm).resolve_left ha
  let φ := coneMap (R := R) (G := G)
  have inj : Function.Injective φ := mapDomain_injective Subtype.val_injective
  obtain ⟨f, g, hf, row⟩ := generating_rows_group solve (φ a) (φ c) ((map_ne_zero_iff _ inj).mpr ha)
  obtain ⟨k, _, hk⟩ := row (φ a) (φ c) (mul_comm ..)
  have hg : g ≠ 0 := fun h ↦ hc ((map_eq_zero_iff _ inj).mp (by rw [hk, h, mul_zero]))
  let s := min (leastExp f hf) (leastExp g hg)
  obtain ⟨F, hF⟩ := monomial_shift_mem hf (g := -s)
    (by simpa only [add_comm, ← sub_eq_add_neg] using sub_nonneg.mpr (min_le_left _ _))
  obtain ⟨G', hG⟩ := monomial_shift_mem hg (g := -s)
    (by simpa only [add_comm, ← sub_eq_add_neg] using sub_nonneg.mpr (min_le_right _ _))
  have cancel (x y : AddMonoidAlgebra R G) :
      (single s 1 * x) * (single (-s) 1 * y) = x * y := by
    rw [mul_mul_mul_comm, single_mul_single, add_neg_cancel, one_mul, ← one_def, one_mul]
  have hn : F ≠ 0 := fun h ↦ hf (by
    have := cancel 1 f
    rw [← hF, h, map_zero, mul_zero, one_mul] at this
    exact this.symm)
  refine ⟨F, G', hn, fun x y he ↦ ?_⟩
  obtain ⟨q, hx, hy⟩ := row (φ x) (φ y) (by simpa only [map_mul] using congrArg φ he)
  by_cases hq : q = 0
  · exact ⟨0, by apply inj; simp [hx, hq], by apply inj; simp [hy, hq]⟩
  have pos {z} {p : AddMonoidAlgebra R G} (hp : p ≠ 0) (he : φ z = q * p) :
      0 ≤ leastExp q hq + leastExp p hp :=
    (mem_range_coneMap _).mp ⟨z, he⟩ _ (leastExp_add_mem hq hp)
  obtain ⟨Q, hQ⟩ := monomial_shift_mem hq (g := s) (by
    rw [show s = min (leastExp f hf) (leastExp g hg) from rfl, add_comm, ← min_add_add_left]
    exact le_min (pos hf hx) (pos hg hy))
  exact ⟨Q, inj (by rw [map_mul, hx, hQ, hF, cancel]), inj (by rw [map_mul, hy, hQ, hG, cancel])⟩

end AddMonoidAlgebra
