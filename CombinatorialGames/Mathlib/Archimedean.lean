import Mathlib.Algebra.Order.Archimedean.Class

namespace ArchimedeanClass
variable {M : Type*} [LinearOrder M] [CommRing M] [IsStrictOrderedRing M]

attribute [induction_eliminator] ind

theorem mk_mul_le_of_le {x₁ y₁ x₂ y₂ : M} (hx : mk x₁ ≤ mk x₂) (hy : mk y₁ ≤ mk y₂) :
    mk (x₁ * y₁) ≤ mk (x₂ * y₂) := by
  obtain ⟨m, hm⟩ := hx
  obtain ⟨n, hn⟩ := hy
  use m * n
  convert mul_le_mul hm hn (abs_nonneg _) (nsmul_nonneg (abs_nonneg _) _) using 1 <;>
    simp_rw [ArchimedeanOrder.val_of, abs_mul]
  ring

instance : Add (ArchimedeanClass M) where
  add := Quotient.lift₂ (fun x y ↦ .mk <| x.val * y.val) fun _ _ _ _ hx hy ↦
    (mk_mul_le_of_le hx.le hy.le).antisymm (mk_mul_le_of_le hx.ge hy.ge)

@[simp]
theorem mk_mul (x y : M) : mk (x * y) = mk x + mk y :=
  rfl

instance : AddCommMagma (ArchimedeanClass M) where
  add_comm x y := by
    induction x with | mk x =>
    induction y with | mk y =>
    rw [← mk_mul, mul_comm, mk_mul]

@[simp]
theorem top_add (x : ArchimedeanClass M) : ⊤ + x = ⊤ := by
  induction x with | mk x =>
  rw [← mk_zero, ← mk_mul, zero_mul]

@[simp]
theorem add_top (x : ArchimedeanClass M) : x + ⊤ = ⊤ := by
  rw [add_comm, top_add]

end ArchimedeanClass
