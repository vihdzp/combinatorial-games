/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang, Violeta Hernández Palacios
-/
import Mathlib.Algebra.Order.Archimedean.Class
import Mathlib.Algebra.Order.Hom.Ring
import Mathlib.Algebra.Order.Ring.Archimedean
import Mathlib.Algebra.Order.Group.DenselyOrdered

-- https://github.com/leanprover-community/mathlib4/pull/29611

variable {R S : Type*} [LinearOrder R] [LinearOrder S]

namespace ArchimedeanClass

theorem mk_le_mk_iff_denselyOrdered [CommRing R] [IsStrictOrderedRing R]
    [Ring S] [IsStrictOrderedRing S] [DenselyOrdered R] [Archimedean R] {x y : S}
    (f : R →+* S) (hf : StrictMono f) : mk x ≤ mk y ↔ ∃ q : R, 0 < f q ∧ f q * |y| ≤ |x| := by
  have H {q} : 0 < f q ↔ 0 < q := by simpa using hf.lt_iff_lt (a := 0)
  constructor
  · rintro ⟨(_ | n), hn⟩
    · simp_all [exists_zero_lt]
    · obtain ⟨q, hq₀, hq⟩ := exists_nsmul_lt_of_pos (one_pos (α := R)) (n + 1)
      refine ⟨q, H.2 hq₀, le_of_mul_le_mul_left ?_ n.cast_add_one_pos⟩
      simpa [← mul_assoc] using mul_le_mul (hf hq).le hn (abs_nonneg y) (by simp)
  · rintro ⟨q, hq₀, hq⟩
    have hq₀' := H.1 hq₀
    obtain ⟨n, hn⟩ := exists_lt_nsmul hq₀' 1
    refine ⟨n, le_of_mul_le_mul_left ?_ hq₀⟩
    have h : 0 ≤ f (n • q) := by
      rw [← f.map_zero]
      exact hf.monotone (nsmul_nonneg hq₀'.le n)
    simpa [mul_comm, mul_assoc] using mul_le_mul (hf hn).le hq (mul_nonneg hq₀.le (abs_nonneg y)) h

theorem mk_le_mk_iff_ratCast {x y : R} [Field R] [IsStrictOrderedRing R] :
    mk x ≤ mk y ↔ ∃ q : ℚ, 0 < q ∧ q * |y| ≤ |x| := by
  have := IsOrderedRing.toIsStrictOrderedRing R
  simpa using mk_le_mk_iff_denselyOrdered (Rat.castHom _) Rat.cast_strictMono (x := x)

end ArchimedeanClass
