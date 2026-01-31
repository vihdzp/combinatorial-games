import CombinatorialGames.Mathlib.CyclicGroup
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90

lemma ZMod.finEquiv_apply {n : ℕ} [hn : NeZero n] (i : Fin n) : ZMod.finEquiv n i = i :=
  n.casesOn (fun hn _ => (hn.out rfl).elim)
    (fun _ hn i => (@ZMod.natCast_zmod_val _ hn (by unfold ZMod; exact i)).symm) hn i

-- written by Aaron Liu
-- the proof follows Keith Conrad, *Linear Independence of Characters*

namespace groupCohomology
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- Hilbert's Theorem 90: given a finite cyclic Galois extension `L/K`, an element `x : L` such
that `Tr_{L/K}(x) = 0`, and a generator `g` of `Gal(L/K)`, there exists `y : L`
such that `y - g y = x`. -/
theorem exists_sub_of_trace_eq_zero {g : Gal(L/K)} (hg : ∀ x, x ∈ Subgroup.zpowers g) {x : L}
    (hx : Algebra.trace K L x = 0) : ∃ y : L, y - g y = x := by
  have ht := Algebra.trace_ne_zero K L
  rw [← DFunLike.coe_injective.ne_iff, Function.ne_iff] at ht
  obtain ⟨z, hz⟩ := ht
  let n := Module.finrank K L
  have : NeZero n := ⟨Module.finrank_pos.ne'⟩
  let e : Multiplicative (ZMod n) ≃* Gal(L/K) :=
    zmodMulEquivOfGeneratorOfCardEq hg (IsGalois.card_aut_eq_finrank K L)
  have he : e (Multiplicative.ofAdd 1) = g :=
    zmodMulEquivOfGeneratorOfCardEq_apply_ofAdd_one hg (IsGalois.card_aut_eq_finrank K L)
  let f : L →ₗ[K] L := ∑ i : ZMod n,
    (∑ j : Fin (i.val + 1), e (Multiplicative.ofAdd (Int.cast j.1)) x) •
      (e (Multiplicative.ofAdd i)).toLinearMap
  refine ⟨f z / algebraMap K L (Algebra.trace K L z), ?_⟩
  rw [map_div₀, AlgHomClass.commutes, ← sub_div, div_eq_iff (by simpa using hz)]
  unfold f
  rw [LinearMap.sum_apply, map_sum,
    ← Equiv.sum_comp (Equiv.addLeft 1), ← Finset.sum_sub_distrib]
  have ht y : ∑ i : Multiplicative (ZMod n), g (e i y) = algebraMap K L (Algebra.trace K L y) := by
    rw [trace_eq_sum_automorphisms, ← (e.toEquiv.trans (Equiv.mulLeft g)).sum_comp]
    simp
  rw [← ht, Finset.mul_sum, ← Multiplicative.ofAdd.sum_comp]
  apply Fintype.sum_congr
  intro i
  simp only [LinearMap.smul_apply, smul_eq_mul, map_mul,
    Equiv.coe_addLeft, AlgEquiv.toLinearMap_apply]
  rw [map_sum, ofAdd_add, map_mul, he, AlgEquiv.mul_apply, ← sub_mul, add_comm 1 i]
  refine congrArg (· * _) ?_
  by_cases h : (i + 1).val = i.val + 1
  · rw [h, Fin.sum_univ_succ, add_sub_assoc, Fin.val_zero, Nat.cast_zero, Int.cast_zero,
      ofAdd_zero, map_one, AlgEquiv.one_apply, add_eq_left, ← Finset.sum_sub_distrib]
    apply Fintype.sum_eq_zero
    intro j
    rw [Fin.val_succ, Nat.add_comm j.val 1, Nat.cast_add, Int.cast_add,
      ofAdd_add, Nat.cast_one, Int.cast_one, map_mul, he, AlgEquiv.mul_apply, sub_self]
  obtain hn | hn := eq_or_ne n 1
  · have ho : ∀ (o : ZMod n), o.val = 0 := by rw [hn]; decide
    have : Subsingleton (ZMod n) := by rw [hn]; infer_instance
    have : Subsingleton (Gal(L/K)) := e.symm.subsingleton
    rw [ho, ho, Fin.sum_univ_one, Fin.sum_univ_one, ← he, ← AlgEquiv.mul_apply, ← map_mul,
      Subsingleton.eq_one (Multiplicative.ofAdd _), Subsingleton.eq_one (_ * _),
      sub_self, ← (algebraMap K L).map_zero, ← hx, trace_eq_sum_automorphisms,
      Fintype.sum_subsingleton _ .refl, AlgEquiv.coe_refl, id_eq]
  have hnv : n ≤ i.val + (1 : ZMod n).val := by
    contrapose! h
    rw [← ZMod.val_one'' hn]
    exact ZMod.val_add_of_lt h
  have := ZMod.val_add_of_le hnv
  have := ZMod.val_one'' hn
  have := ZMod.val_lt i
  rw [show (i + 1).val = 0 by omega, show i.val + 1 = n by omega, Fin.sum_univ_one,
    Fin.val_zero, Nat.cast_zero, Int.cast_zero, ofAdd_zero, map_one, AlgEquiv.one_apply,
    sub_eq_self, ← (algebraMap K L).map_zero, ← hx, ← ht,
    ← ((ZMod.finEquiv n).toEquiv.trans Multiplicative.ofAdd).sum_comp]
  simp [ZMod.finEquiv_apply]

end groupCohomology
