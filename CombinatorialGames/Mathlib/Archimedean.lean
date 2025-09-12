/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang, Violeta Hernández Palacios
-/
import Mathlib.Algebra.Order.Archimedean.Class
import Mathlib.Algebra.Order.Hom.Ring
import Mathlib.Algebra.Order.Ring.Archimedean
import Mathlib.Algebra.Order.Group.DenselyOrdered

-- https://github.com/leanprover-community/mathlib4/pull/28187

variable {R S : Type*} [LinearOrder R] [LinearOrder S]
variable [CommRing R] [IsStrictOrderedRing R]

namespace ArchimedeanClass
section Ring

variable [CommRing S] [IsStrictOrderedRing S]

@[simp]
theorem orderHom_zero (f : S →+o R) : orderHom f 0 = mk (f 1) := by
  rw [← mk_one, orderHom_mk]

@[simp]
theorem mk_eq_zero_of_archimedean [Archimedean S] {x : S} (h : x ≠ 0) : mk x = 0 := by
  have : Nontrivial S := ⟨_, _, h⟩
  exact mk_eq_mk_of_archimedean h one_ne_zero

theorem eq_zero_or_top_of_archimedean [Archimedean S] (x : ArchimedeanClass S) : x = 0 ∨ x = ⊤ := by
  induction x with | mk x
  obtain rfl | h := eq_or_ne x 0 <;> simp_all

/-- See `mk_map_of_archimedean'` for a version taking `M →+*o R`. -/
theorem mk_map_of_archimedean [Archimedean S] (f : S →+o R) {x : S} (h : x ≠ 0) :
    mk (f x) = mk (f 1) := by
  rw [← orderHom_mk, mk_eq_zero_of_archimedean h, orderHom_zero]

/-- See `mk_map_of_archimedean` for a version taking `M →+o R`. -/
theorem mk_map_of_archimedean' [Archimedean S] (f : S →+*o R) {x : S} (h : x ≠ 0) :
    mk (f x) = 0 := by
  simpa using mk_map_of_archimedean f.toOrderAddMonoidHom h

@[simp]
theorem mk_intCast {n : ℤ} (h : n ≠ 0) : mk (n : S) = 0 :=
  mk_map_of_archimedean' ⟨Int.castRingHom S, fun _ ↦ by simp⟩ h

@[simp]
theorem mk_natCast {n : ℕ} (h : n ≠ 0) : mk (n : S) = 0 := by
  rw [← Int.cast_natCast]
  exact mk_intCast (mod_cast h)

end Ring

section Ring

variable [Ring S] [IsStrictOrderedRing S]

private theorem mk_le_mk_iff_denselyOrdered' [DenselyOrdered R] [Archimedean R] {x y : S}
    (f : R →+*o S) (hf : StrictMono f) (h : 0 < y) :
    mk x ≤ mk y ↔ ∃ q : R, 0 < f q ∧ f q * |y| ≤ |x| := by
  have H {q} : 0 < f q ↔ 0 < q := by simpa using hf.lt_iff_lt (a := 0)
  constructor
  · rintro ⟨(_ | n), hn⟩
    · simp_all
    · obtain ⟨q, hq₀, hq⟩ := exists_nsmul_lt_of_pos (one_pos (α := R)) (n + 1)
      refine ⟨q, H.2 hq₀, le_of_mul_le_mul_left ?_ n.cast_add_one_pos⟩
      simpa [← mul_assoc] using mul_le_mul (hf hq).le hn (abs_nonneg y) (by simp)
  · rintro ⟨q, hq₀, hq⟩
    have hq₀' := H.1 hq₀
    obtain ⟨n, hn⟩ := exists_lt_nsmul hq₀' 1
    refine ⟨n, le_of_mul_le_mul_left ?_ hq₀⟩
    have h : 0 ≤ f (n • q) := by
      rw [← f.map_zero]
      exact f.monotone' (nsmul_nonneg hq₀'.le n)
    simpa [mul_comm, mul_assoc] using mul_le_mul (hf hn).le hq (mul_nonneg hq₀.le (abs_nonneg y)) h

theorem mk_le_mk_iff_denselyOrdered [DenselyOrdered R] [Archimedean R] {x y : S}
    (f : R →+*o S) (hf : StrictMono f) :
    mk x ≤ mk y ↔ ∃ q : R, 0 < f q ∧ f q * |y| ≤ |x| := by
  obtain hy | rfl | hy := lt_trichotomy y 0
  · simpa using mk_le_mk_iff_denselyOrdered' f hf (neg_pos.2 hy)
  · have : ∃ q, 0 < f q := ⟨1, by simp⟩
    simpa
  · exact mk_le_mk_iff_denselyOrdered' f hf hy

def _root_.Rat.castOrderRingHom [Field R] [IsStrictOrderedRing R] : ℚ →+*o R where
  monotone' := Rat.cast_mono
  __ := Rat.castHom _

end Ring

theorem mk_le_mk_iff_ratCast [Field S] [IsOrderedRing S] {x y : S} :
    mk x ≤ mk y ↔ ∃ q : ℚ, 0 < q ∧ q * |y| ≤ |x| := by
  have := IsOrderedRing.toIsStrictOrderedRing S
  simpa using mk_le_mk_iff_denselyOrdered Rat.castOrderRingHom Rat.cast_strictMono (x := x) (y := y)

end ArchimedeanClass
