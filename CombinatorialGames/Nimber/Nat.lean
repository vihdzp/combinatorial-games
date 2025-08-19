import CombinatorialGames.Nimber.SimplestExtension.Algebraic

alias! /-- The natural numbers, endowed with nim operations. -/ NatNimber Nat

namespace NatNimber

instance : LinearOrder NatNimber := Nat.instLinearOrder

instance : Lean.ToExpr NatNimber where
  toExpr x := .app (.const `NatNimber.of []) (Lean.toExpr x.val)
  toTypeExpr := .const `NatNimber []

instance : ToString NatNimber where
  toString x := "∗" ++ x.val.repr

@[simp] theorem lt_one_iff_zero {a : NatNimber} : a < 1 ↔ a = 0 := Nat.lt_one_iff
@[simp] theorem one_le_iff_ne_zero {a : NatNimber} : 1 ≤ a ↔ a ≠ 0 := Nat.one_le_iff_ne_zero
theorem le_one_iff {a : NatNimber} : a ≤ 1 ↔ a = 0 ∨ a = 1 := Nat.le_one_iff_eq_zero_or_eq_one

private theorem lt_of_lt_pow_pow {n k : ℕ} (hn : 2 ≤ n) (hk : k < 2 ^ 2 ^ n.log2.log2) : k < n := by
  simp_rw [Nat.log2_eq_log_two] at hk
  by_contra! hnk
  apply (Nat.log_mono_right (Nat.log_mono_right hnk)).not_gt
  apply Nat.log_lt_of_lt_pow _ (Nat.log_lt_of_lt_pow _ hk)
  · simpa using hn.trans hnk
  · aesop

private theorem div_pow_pow_lt {n : ℕ} : n / 2 ^ 2 ^ n.log2.log2 < 2 ^ 2 ^ n.log2.log2 := by
  simp_rw [Nat.log2_eq_log_two]
  rw [Nat.div_lt_iff_lt_mul (pow_pos zero_lt_two _), ← pow_add, ← two_mul, ← pow_succ']
  iterate 2 apply Nat.lt_pow_of_log_lt one_lt_two
  exact Nat.lt_succ_self _

private theorem div_pow_pow_ne_zero {n : ℕ} (hn : 2 ≤ n) : n / 2 ^ 2 ^ n.log2.log2 ≠ 0 := by
  rw [← Nat.pos_iff_ne_zero]
  apply Nat.div_pos _ (pow_pos zero_lt_two _)
  trans 2 ^ n.log2
  · rw [pow_le_pow_iff_right₀ one_lt_two, ← Nat.le_log2]
    simpa [Nat.log2_eq_log_two]
  · apply Nat.log2_self_le
    aesop

private theorem pow_pow_le_mul_add {a : ℕ} (t b : ℕ) (ha : a ≠ 0) :
    2 ^ 2 ^ t ≤ 2 ^ 2 ^ t * a + b := by
  apply le_add_of_le_left; simpa [Nat.one_le_iff_ne_zero]

private theorem two_le_pow_pow_mul_add {a : ℕ} (t b : ℕ) (ha : a ≠ 0) : 2 ≤ 2 ^ 2 ^ t * a + b := by
  apply (pow_pow_le_mul_add t b ha).trans'
  conv_lhs => rw [← Nat.pow_one 2, ← Nat.pow_zero 2]
  rw [Nat.pow_le_pow_iff_right, Nat.pow_le_pow_iff_right] <;> simp

private theorem log2_log2_mul_add {t a b : ℕ}
    (ha : a < 2 ^ 2 ^ t) (ha₀ : a ≠ 0) (hb : b < 2 ^ 2 ^ t) : (2 ^ 2 ^ t * a + b).log2.log2 = t := by
  have h : 2 ^ 2 ^ t * a + b ≠ 0 := by simp_all
  rw [Nat.log2_eq_log_two, Nat.log_eq_iff]
  · constructor
    · rw [Nat.le_log2 h]
      exact pow_pow_le_mul_add _ _ ha₀
    · rw [Nat.log2_lt h, pow_add, pow_mul, pow_one, pow_two]
      apply (add_lt_add_left hb _).trans_le
      rw [← mul_add_one]
      exact mul_le_mul_left' ha _
  · simp [Nat.log2_eq_log_two, two_le_pow_pow_mul_add t b ha₀]

/-- Build data by induction on `n.log2.log2`. -/
def splitRec {motive : NatNimber → Sort*} (zero : motive 0) (one : motive 1)
    (ind : ∀ t, (∀ n < 2 ^ 2 ^ t, motive (of n)) → ∀ a < 2 ^ 2 ^ t, a ≠ 0 → ∀ b < 2 ^ 2 ^ t,
      motive (of (2 ^ 2 ^ t * a + b))) (n : NatNimber) : motive n :=
  if h₀ : n = 0 then cast (congrArg motive h₀.symm) zero else
  if h₁ : n = 1 then cast (congrArg motive h₁.symm) one else by
  have h₂ : 2 ≤ n.val := by by_contra!; interval_cases _ : n.val <;> simp_all
  have H : of (_ + _) = n := Nat.div_add_mod n.val (2 ^ 2 ^ n.val.log2.log2)
  apply cast (congrArg motive H) (ind ..)
  · exact fun k hk ↦ splitRec zero one ind k
  · exact div_pow_pow_lt
  · exact div_pow_pow_ne_zero h₂
  · exact Nat.mod_lt _ (pow_pos zero_lt_two _)
termination_by n
decreasing_by exact lt_of_lt_pow_pow h₂ hk

@[simp]
theorem splitRec_zero {motive : NatNimber → Sort*} (zero : motive 0) (one : motive 1)
    (ind : ∀ t, (∀ k < 2 ^ 2 ^ t, motive (of k)) → ∀ a < 2 ^ 2 ^ t, a ≠ 0 → ∀ b < 2 ^ 2 ^ t,
      motive (of (2 ^ 2 ^ t * a + b))) : splitRec zero one ind 0 = zero := by
  rw [splitRec]
  simp

@[simp]
theorem splitRec_one {motive : NatNimber → Sort*} (zero : motive 0) (one : motive 1)
    (ind : ∀ t, (∀ k < 2 ^ 2 ^ t, motive (of k)) → ∀ a < 2 ^ 2 ^ t, a ≠ 0 → ∀ b < 2 ^ 2 ^ t,
      motive (of (2 ^ 2 ^ t * a + b))) : splitRec zero one ind 1 = one := by
  rw [splitRec]
  simp

theorem splitRec_mul_add {motive : NatNimber → Sort*} (zero : motive 0) (one : motive 1)
    (ind : ∀ t, (∀ k < 2 ^ 2 ^ t, motive (of k)) → ∀ a < 2 ^ 2 ^ t, a ≠ 0 → ∀ b < 2 ^ 2 ^ t,
      motive (of (2 ^ 2 ^ t * a + b))) {a b t : ℕ}
    (ha : a < 2 ^ 2 ^ t) (ha₀ : a ≠ 0) (hb : b < 2 ^ 2 ^ t) :
    splitRec zero one ind (of (2 ^ 2 ^ t * a + b)) =
    ind t (fun k _ ↦ splitRec zero one ind k) a ha ha₀ b hb := by
  have h := log2_log2_mul_add ha ha₀ hb
  rw [splitRec, dif_neg, dif_neg, cast_eq_iff_heq]
  congr!
  · rw [val_of, h, Nat.mul_add_div, Nat.div_eq_of_lt hb, add_zero]
    exact pow_pos zero_lt_two _
  · rw [val_of, h, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]
  · simp_all
  · have := two_le_pow_pow_mul_add t b ha₀
    aesop

/-- Build data by induction on `max m.log2.log2 n.log2.log2`. -/
def splitRec₂ {motive : NatNimber → NatNimber → Sort*}
    (zero_zero : motive 0 0) (zero_one : motive 0 1) (one_zero : motive 1 0) (one_one : motive 1 1)
    (ind : ∀ t, (∀ m < 2 ^ 2 ^ t, ∀ n < 2 ^ 2 ^ t, motive (of m) (of n)) →
      ∀ a < 2 ^ 2 ^ t, ∀ b < 2 ^ 2 ^ t, ∀ c < 2 ^ 2 ^ t, ∀ d < 2 ^ 2 ^ t, a ≠ 0 ∨ c ≠ 0 →
      motive (of (2 ^ 2 ^ t * a + b)) (of (2 ^ 2 ^ t * c + d))) (m n : NatNimber) : motive m n :=
  if h₀₀ : m = 0 ∧ n = 0 then cast (congrArg₂ motive h₀₀.1.symm h₀₀.2.symm) zero_zero else
  if h₀₁ : m = 0 ∧ n = 1 then cast (congrArg₂ motive h₀₁.1.symm h₀₁.2.symm) zero_one else
  if h₁₀ : m = 1 ∧ n = 0 then cast (congrArg₂ motive h₁₀.1.symm h₁₀.2.symm) one_zero else
  if h₁₁ : m = 1 ∧ n = 1 then cast (congrArg₂ motive h₁₁.1.symm h₁₁.2.symm) one_one else by
  let M := max m.val n.val
  have h₂ : 2 ≤ M := by sorry
  have Hm : of (_ + _) = m := Nat.div_add_mod m.val (2 ^ 2 ^ M.log2.log2)
  have Hn : of (_ + _) = n := Nat.div_add_mod n.val (2 ^ 2 ^ M.log2.log2)
  apply cast (congrArg₂ motive Hm Hn) (ind ..)
  · exact fun k hk ↦ splitRec₂ zero one ind k
  · exact div_pow_pow_lt
  · exact div_pow_pow_ne_zero h₂
  · exact Nat.mod_lt _ (pow_pos zero_lt_two _)
termination_by n
decreasing_by exact lt_of_lt_pow_pow h₂ hk

#exit

@[simp]
theorem splitRec_zero {motive : NatNimber → Sort*} (zero : motive 0) (one : motive 1)
    (ind : ∀ t, (∀ k < 2 ^ 2 ^ t, motive (of k)) → ∀ a < 2 ^ 2 ^ t, a ≠ 0 → ∀ b < 2 ^ 2 ^ t,
      motive (of (2 ^ 2 ^ t * a + b))) : splitRec zero one ind 0 = zero := by
  rw [splitRec]
  simp

@[simp]
theorem splitRec_one {motive : NatNimber → Sort*} (zero : motive 0) (one : motive 1)
    (ind : ∀ t, (∀ k < 2 ^ 2 ^ t, motive (of k)) → ∀ a < 2 ^ 2 ^ t, a ≠ 0 → ∀ b < 2 ^ 2 ^ t,
      motive (of (2 ^ 2 ^ t * a + b))) : splitRec zero one ind 1 = one := by
  rw [splitRec]
  simp

theorem splitRec_mul_add {motive : NatNimber → Sort*} (zero : motive 0) (one : motive 1)
    (ind : ∀ t, (∀ k < 2 ^ 2 ^ t, motive (of k)) → ∀ a < 2 ^ 2 ^ t, a ≠ 0 → ∀ b < 2 ^ 2 ^ t,
      motive (of (2 ^ 2 ^ t * a + b))) {a b t : ℕ}
    (ha : a < 2 ^ 2 ^ t) (ha₀ : a ≠ 0) (hb : b < 2 ^ 2 ^ t) :
    splitRec zero one ind (of (2 ^ 2 ^ t * a + b)) =
    ind t (fun k _ ↦ splitRec zero one ind k) a ha ha₀ b hb := by
  have h := log2_log2_mul_add ha ha₀ hb
  rw [splitRec, dif_neg, dif_neg, cast_eq_iff_heq]
  congr!
  · rw [val_of, h, Nat.mul_add_div, Nat.div_eq_of_lt hb, add_zero]
    exact pow_pos zero_lt_two _
  · rw [val_of, h, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]
  · simp_all
  · have := two_le_pow_pow_mul_add t b ha₀
    aesop

end NatNimber
