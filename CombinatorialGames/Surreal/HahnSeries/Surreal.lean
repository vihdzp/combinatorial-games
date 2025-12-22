import CombinatorialGames.Surreal.HahnSeries.Basic
import CombinatorialGames.Surreal.Birthday.Basic

universe u

open IGame Order Set

attribute [-simp] Ordinal.add_one_eq_succ

noncomputable section

/-! ### Hahn series as games -/

namespace SurrealHahnSeries

/-- A common base for both `truncLT` and `truncGT`. -/
private def truncAux (x : SurrealHahnSeries) (R : ℝ → ℝ → Prop) : Set SurrealHahnSeries :=
  range fun i : (j : x.support) × {r // R r (x.coeff j)} ↦ x.trunc i.1 + single i.1 i.2

/-- We write `x ≺ y` whenever `x = y.trunc i + single i r` for some `i ∈ y.support` and
`r < y.coeff i`.

When `y.length` is a limit ordinal, the series with `x ≺ y` describe the left options of
`toIGame y`. -/
def truncLT (x : SurrealHahnSeries) : Set SurrealHahnSeries :=
  truncAux x (· < ·)

notation:50 x:50 " ≺ " y:50 => x ∈ truncLT y
recommended_spelling "truncLT" for "≺" in [«term_≺_»]

/-- We write `x ≻ y` whenever `x = y.trunc i + single i r` for some `i ∈ y.support` and
`r > y.coeff i`.

When `y.length` is a limit ordinal, the series with `x ≻ y` describe the right options of
`toIGame y`. -/
def truncGT (x : SurrealHahnSeries) : Set SurrealHahnSeries :=
  truncAux x (· > ·)

local notation:50 x:50 " ≻ " y:50 => x ∈ truncGT y
recommended_spelling "truncGT" for "≻" in [«term_≺_»]

private theorem truncAux_def {x y : SurrealHahnSeries} {R : ℝ → ℝ → Prop} :
    x ∈ truncAux y R ↔ ∃ i ∈ y.support, ∃ r : ℝ, R r (y.coeff i) ∧ y.trunc i + single i r = x := by
  simp [truncAux]

theorem truncLT_def {x y : SurrealHahnSeries} :
    x ≺ y ↔ ∃ i ∈ y.support, ∃ r : ℝ, r < y.coeff i ∧ y.trunc i + single i r = x :=
  truncAux_def

theorem truncGT_def {x y : SurrealHahnSeries} :
    x ≻ y ↔ ∃ i ∈ y.support, ∃ r : ℝ, y.coeff i < r ∧ y.trunc i + single i r = x :=
  truncAux_def

private theorem forall_mem_truncAux {y : SurrealHahnSeries}
    {P : SurrealHahnSeries → Prop} {R : ℝ → ℝ → Prop} :
    (∀ x ∈ truncAux y R, P x) ↔
      ∀ i ∈ y.support, ∀ r : ℝ, R r (y.coeff i) → P (y.trunc i + single i r) := by
  aesop (add simp [truncAux])

theorem forall_mem_truncLT {y : SurrealHahnSeries} {P : SurrealHahnSeries → Prop} :
    (∀ x ∈ truncLT y, P x) ↔
      ∀ i ∈ y.support, ∀ r : ℝ, r < y.coeff i → P (y.trunc i + single i r) :=
  forall_mem_truncAux

theorem forall_mem_truncGT {y : SurrealHahnSeries} {P : SurrealHahnSeries → Prop} :
    (∀ x ∈ truncGT y, P x) ↔
      ∀ i ∈ y.support, ∀ r : ℝ, y.coeff i < r → P (y.trunc i + single i r) :=
  forall_mem_truncAux

theorem exists_mem_truncAux {y : SurrealHahnSeries}
    {P : SurrealHahnSeries → Prop} {R : ℝ → ℝ → Prop} :
    (∃ x ∈ truncAux y R, P x) ↔
      ∃ i ∈ y.support, ∃ r : ℝ, R r (y.coeff i) ∧ P (y.trunc i + single i r) := by
  aesop (add simp [truncAux])

theorem exists_mem_truncLT {y : SurrealHahnSeries} {P : SurrealHahnSeries → Prop} :
    (∃ x ∈ truncLT y, P x) ↔
      ∃ i ∈ y.support, ∃ r : ℝ, r < y.coeff i ∧ P (y.trunc i + single i r) :=
  exists_mem_truncAux

theorem exists_mem_truncGT {y : SurrealHahnSeries} {P : SurrealHahnSeries → Prop} :
    (∃ x ∈ truncGT y, P x) ↔
      ∃ i ∈ y.support, ∃ r : ℝ, y.coeff i < r ∧ P (y.trunc i + single i r) :=
  exists_mem_truncAux

private theorem truncAux_zero (R : ℝ → ℝ → Prop) : truncAux 0 R = ∅ := by
  unfold truncAux; simp

@[simp] theorem truncLT_zero : truncLT 0 = ∅ := truncAux_zero _
@[simp] theorem truncGT_zero : truncGT 0 = ∅ := truncAux_zero _

private theorem trunc_add_single_truncAux {x : SurrealHahnSeries} {i : Surreal} {r : ℝ}
    {R : ℝ → ℝ → Prop} (hi : i ∈ x.support) (hr : R r (x.coeff i)) :
    x.trunc i + single i r ∈ truncAux x R := by
  unfold truncAux
  aesop

theorem trunc_add_single_truncLT {x : SurrealHahnSeries} {i : Surreal} {r : ℝ}
    (hi : i ∈ x.support) (hr : r < x.coeff i) : x.trunc i + single i r ≺ x :=
  trunc_add_single_truncAux hi hr

theorem trunc_add_single_truncGT {x : SurrealHahnSeries} {i : Surreal} {r : ℝ}
    (hi : i ∈ x.support) (hr : x.coeff i < r) : x.trunc i + single i r ≻ x :=
  trunc_add_single_truncAux hi hr

instance small_truncAux (x : SurrealHahnSeries.{u}) (R : ℝ → ℝ → Prop) : Small.{u} (truncAux x R) :=
  by unfold truncAux; infer_instance

instance small_truncLT (x : SurrealHahnSeries.{u}) : Small.{u} (truncLT x) := small_truncAux ..
instance small_truncGT (x : SurrealHahnSeries.{u}) : Small.{u} (truncGT x) := small_truncAux ..

private theorem length_le_of_truncAux {x y : SurrealHahnSeries} {R : ℝ → ℝ → Prop}
    (h : x ∈ truncAux y R) : x.length ≤ y.length := by
  obtain ⟨⟨i, hi⟩, rfl⟩ := h
  apply (length_add_single_le ..).trans
  · rw [add_one_le_iff]
    exact length_trunc_lt i.2
  · simp

private theorem length_lt_of_truncAux {x y : SurrealHahnSeries} (hy : IsSuccPrelimit y.length)
    {R : ℝ → ℝ → Prop} (h : x ∈ truncAux y R) : x.length < y.length := by
  obtain ⟨⟨i, hi⟩, rfl⟩ := h
  apply (length_add_single_le ..).trans_lt
  · exact hy.add_one_lt <| length_trunc_lt i.2
  · simp

theorem length_le_of_truncLT {x y : SurrealHahnSeries} (h : x ≺ y) : x.length ≤ y.length :=
  length_le_of_truncAux h

theorem length_le_of_truncGT {x y : SurrealHahnSeries} (h : x ≻ y) : x.length ≤ y.length :=
  length_le_of_truncAux h

theorem length_lt_of_truncLT {x y : SurrealHahnSeries} (hy : IsSuccPrelimit y.length) (h : x ≺ y) :
    x.length < y.length :=
  length_lt_of_truncAux hy h

theorem length_lt_of_truncGT {x y : SurrealHahnSeries} (hy : IsSuccPrelimit y.length) (h : x ≻ y) :
    x.length < y.length :=
  length_lt_of_truncAux hy h

theorem lt_of_truncLT {x y : SurrealHahnSeries} (h : x ≺ y) : x < y := by
  obtain ⟨⟨⟨i, hi⟩, s, hs⟩, rfl⟩ := h
  rw [lt_def]
  use i
  aesop

theorem gt_of_truncGT {x y : SurrealHahnSeries} (h : x ≻ y) : y < x := by
  obtain ⟨⟨⟨i, hi⟩, s, hs⟩, rfl⟩ := h
  rw [lt_def]
  use i
  aesop

private theorem truncAux_truncIdx_ssubset {x : SurrealHahnSeries} {R : ℝ → ℝ → Prop} {i : Ordinal}
    (h : i < x.length) (hR : ∀ r, ∃ s ≠ 0, R s r) : truncAux (truncIdx x i) R ⊂ truncAux x R := by
  constructor
  · intro y hy
    rw [truncAux_def] at hy ⊢
    obtain ⟨a, ha, r, hr, rfl⟩ := hy
    refine ⟨a, support_truncIdx_subset _ _ ha, r, ?_, ?_⟩
    · rwa [coeff_truncIdx_of_mem le_rfl ha] at hr
    · rw [trunc_truncIdx_of_mem le_rfl ha]
  · rw [not_subset, exists_mem_truncAux]
    obtain ⟨s, hs, hs'⟩ := hR (x.coeff ↑(x.exp ⟨i, h⟩))
    refine ⟨x.exp ⟨i, h⟩, Subtype.coe_prop _, s, hs', fun H ↦ (length_le_of_truncAux H).not_gt ?_⟩
    rw [trunc_exp, length_truncIdx_add_single _ hs, length_truncIdx, Order.lt_add_one_iff]
    exact min_le_left ..

private theorem truncAux_truncIdx_subset {x : SurrealHahnSeries} {R : ℝ → ℝ → Prop} {i : Ordinal}
    (hR : ∀ r, ∃ s ≠ 0, R s r) : truncAux (truncIdx x i) R ⊆ truncAux x R := by
  obtain hi | hi := lt_or_ge i x.length
  · exact (truncAux_truncIdx_ssubset hi hR).le
  · rw [truncIdx_of_le hi]

private theorem truncAux_truncIdx_strictMonoOn {x : SurrealHahnSeries} {R : ℝ → ℝ → Prop}
    (hR : ∀ r, ∃ s ≠ 0, R s r) :
    StrictMonoOn (fun i ↦ truncAux (truncIdx x i) R) (Iio x.length) := by
  intro i hi j hj h
  dsimp
  rw [← min_eq_right h.le, ← truncIdx_truncIdx]
  apply truncAux_truncIdx_ssubset _ hR
  simp_all

private theorem truncAux_truncIdx_mono {x : SurrealHahnSeries} {R : ℝ → ℝ → Prop}
    (hR : ∀ r, ∃ s ≠ 0, R s r) :
    Monotone fun i ↦ truncAux (truncIdx x i) R := by
  intro i j h
  dsimp
  rw [← min_eq_right h, ← truncIdx_truncIdx]
  exact truncAux_truncIdx_subset hR

private theorem truncLT_aux (r : ℝ) : ∃ s ≠ 0, s < r := ⟨min (r - 1) (-1), by grind⟩
private theorem truncGT_aux (r : ℝ) : ∃ s ≠ 0, r < s := ⟨max (r + 1) 1, by grind⟩

theorem truncLT_truncIdx_ssubset {x : SurrealHahnSeries} {i : Ordinal} (h : i < x.length) :
    truncLT (truncIdx x i) ⊂ truncLT x :=
  truncAux_truncIdx_ssubset h truncLT_aux

theorem truncGT_truncIdx_ssubset {x : SurrealHahnSeries} {i : Ordinal} (h : i < x.length) :
    truncGT (truncIdx x i) ⊂ truncGT x :=
  truncAux_truncIdx_ssubset h truncGT_aux

theorem truncLT_truncIdx_subset {x : SurrealHahnSeries} {i : Ordinal} :
    truncLT (truncIdx x i) ⊆ truncLT x :=
  truncAux_truncIdx_subset truncLT_aux

theorem truncGT_truncIdx_subset {x : SurrealHahnSeries} {i : Ordinal} :
    truncGT (truncIdx x i) ⊆ truncGT x :=
  truncAux_truncIdx_subset truncGT_aux

theorem truncLT_truncIdx_strictMonoOn {x : SurrealHahnSeries} :
    StrictMonoOn (fun i ↦ truncLT (truncIdx x i)) (Iio x.length) :=
  truncAux_truncIdx_strictMonoOn truncLT_aux

theorem truncGT_truncIdx_strictMonoOn {x : SurrealHahnSeries} :
    StrictMonoOn (fun i ↦ truncGT (truncIdx x i)) (Iio x.length) :=
  truncAux_truncIdx_strictMonoOn truncGT_aux

theorem truncLT_truncIdx_mono {x : SurrealHahnSeries} :
    Monotone fun i ↦ truncLT (truncIdx x i) :=
  truncAux_truncIdx_mono truncLT_aux

theorem truncGT_truncIdx_mono {x : SurrealHahnSeries} :
    Monotone fun i ↦ truncGT (truncIdx x i) :=
  truncAux_truncIdx_mono truncGT_aux

/-- The game that corresponds to a given surreal Hahn series.

This is an arbitrary representative for `SurrealHahnSeries.toSurreal`, which we use in its place
while we prove that this game is numeric. -/
@[coe]
def toIGame (x : SurrealHahnSeries.{u}) : IGame.{u} :=
  lengthRecOn x (fun _ i r _ _ IH ↦ IH + r * ω^ i.out) fun y hy IH ↦
    !{range fun i : truncLT y ↦ IH i <| length_lt_of_truncLT hy i.2 |
      range fun i : truncGT y ↦ IH i <| length_lt_of_truncGT hy i.2}

instance : Coe SurrealHahnSeries IGame where
  coe := toIGame

theorem toIGame_succ {x : SurrealHahnSeries}
    {i : Surreal} {r : ℝ} (hi : ∀ j ∈ x.support, i < j) (hr : r ≠ 0) :
    toIGame (x + single i r) = toIGame x + r * ω^ i.out :=
  lengthRecOn_succ hi hr

theorem toIGame_succ_equiv {x : SurrealHahnSeries}
    {i : Surreal} {r : ℝ} (hi : ∀ j ∈ x.support, i < j) :
    toIGame (x + single i r) ≈ toIGame x + r * ω^ i.out := by
  obtain rfl | hr := eq_or_ne r 0
  · rw [single_zero, add_zero, antisymmRel_comm, add_equiv_left_iff, ← Surreal.mk_eq_mk]
    simp
  · rw [toIGame_succ hi hr]

theorem toIGame_limit {x : SurrealHahnSeries.{u}} (hx : IsSuccPrelimit x.length) :
    toIGame x = !{toIGame '' truncLT x | toIGame '' truncGT x} := by
  simp_rw [image_eq_range]
  exact lengthRecOn_limit hx

@[simp]
theorem toIGame_zero : toIGame 0 = 0 := by
  rw [toIGame_limit] <;> aesop

theorem leftMoves_toIGame_limit {x : SurrealHahnSeries} (hx : IsSuccPrelimit x.length) :
    (toIGame x)ᴸ = toIGame '' truncLT x := by
  rw [toIGame_limit hx, leftMoves_ofSets]

theorem rightMoves_toIGame_limit {x : SurrealHahnSeries} (hx : IsSuccPrelimit x.length) :
    (toIGame x)ᴿ = toIGame '' truncGT x := by
  rw [toIGame_limit hx, rightMoves_ofSets]

private theorem toIGame_lt_toIGame_of_truncLT {x y : SurrealHahnSeries} (h : x ≺ y)
    [hy' : Numeric y] (IH : ∀ z, length z < y.length → Numeric z) :
    toIGame x < toIGame y := by
  induction y using lengthRecOn generalizing hy' x with
  | succ y i r hi hr IH' =>
    obtain ⟨⟨⟨j, hj⟩, s, hs⟩, rfl⟩ := h
    rw [coeff_add_apply] at hs
    replace hj := union_subset_union_right y.support support_single_subset (support_add_subset hj)
    have hij : i ≤ j := by rw [le_iff_lt_or_eq]; aesop
    dsimp
    rw [trunc_add, trunc_single_of_le hij, add_zero, toIGame_succ hi hr]
    grw [toIGame_succ_equiv (by simp)]
    obtain hj | rfl := hj
    · replace hij := hi _ hj
      rw [coeff_single_of_ne hij.ne, add_zero] at hs
      obtain ⟨t, ht, ht'⟩ := exists_between hs
      have hst : s * ω^ j.out ≈ t * ω^ j.out + ↑(s - t) * ω^ j.out := by
        rw [← Surreal.mk_eq_mk]
        simp [← add_mul]
      grw [hst, ← add_assoc]
      apply add_lt_add _ (Numeric.mul_wpow_lt_mul_wpow_of_neg ..)
      · grw [← toIGame_succ_equiv (by simp)]
        simp_rw [length_add_single hi hr, lt_add_one_iff] at IH
        have := IH _ le_rfl
        apply IH'
        · rw [truncLT_def]
          exact ⟨j, hj, t, ht', rfl⟩
        · exact fun z hz ↦ IH z hz.le
      · rwa [sub_neg]
      · rw [← Surreal.mk_lt_mk]
        simpa
    · rw [trunc_eq_self hi]
      have : y.coeff j = 0 := by
        by_contra h
        exact (hi _ h).false
      simpa [this] using hs
  | limit y hy IH' =>
    apply Numeric.left_lt
    rw [leftMoves_toIGame_limit hy]
    exact mem_image_of_mem _ h

-- TODO: can we more immediately prove this from the previous theorem?
private theorem toIGame_lt_toIGame_of_truncGT {x y : SurrealHahnSeries} (h : x ≻ y)
    [hy' : Numeric y] (IH : ∀ z, length z < y.length → Numeric z) :
    toIGame y < toIGame x := by
  induction y using lengthRecOn generalizing hy' x with
  | succ y i r hi hr IH' =>
    obtain ⟨⟨⟨j, hj⟩, s, hs⟩, rfl⟩ := h
    rw [coeff_add_apply] at hs
    replace hj := union_subset_union_right y.support support_single_subset (support_add_subset hj)
    have hij : i ≤ j := by rw [le_iff_lt_or_eq]; aesop
    dsimp
    rw [trunc_add, trunc_single_of_le hij, add_zero, toIGame_succ hi hr]
    grw [toIGame_succ_equiv (by simp)]
    obtain hj | rfl := hj
    · replace hij := hi _ hj
      rw [coeff_single_of_ne hij.ne, add_zero] at hs
      obtain ⟨t, ht', ht⟩ := exists_between hs
      have hst : s * ω^ j.out ≈ t * ω^ j.out + ↑(s - t) * ω^ j.out := by
        rw [← Surreal.mk_eq_mk]
        simp [← add_mul]
      grw [hst, ← add_assoc]
      apply add_lt_add _ (Numeric.mul_wpow_lt_mul_wpow_of_pos ..)
      · grw [← toIGame_succ_equiv (by simp)]
        simp_rw [length_add_single hi hr, lt_add_one_iff] at IH
        have := IH _ le_rfl
        apply IH'
        · rw [truncGT_def]
          exact ⟨j, hj, t, ht', rfl⟩
        · exact fun z hz ↦ IH z hz.le
      · rwa [sub_pos]
      · rw [← Surreal.mk_lt_mk]
        simpa
    · rw [trunc_eq_self hi]
      have : y.coeff j = 0 := by
        by_contra h
        exact (hi _ h).false
      simpa [this] using hs
  | limit y hy IH' =>
    apply Numeric.lt_right
    rw [rightMoves_toIGame_limit hy]
    exact mem_image_of_mem _ h

private theorem numeric_toIGame' (x : SurrealHahnSeries)
    (IH : ∀ {y z}, length y < x.length → length z < x.length →
      Numeric y ∧ Numeric z ∧ (y < z → toIGame y < toIGame z)) : Numeric x := by
  have IH' {y : SurrealHahnSeries} (hy : y.length < _) := (IH hy hy).1
  cases x using lengthRecOn with
  | succ x i r hi hr =>
    rw [toIGame_succ hi hr]
    have hx : x.length < (x + single i r).length := by
      rw [length_add_single hi hr, lt_add_one_iff]
    have := IH' hx
    infer_instance
  | limit _ hx =>
    rw [toIGame_limit hx, numeric_def]
    aesop (add apply forward safe [length_lt_of_truncLT, length_lt_of_truncGT,
      lt_of_truncLT, gt_of_truncGT, lt_trans])

private theorem toIGame_aux {o : Ordinal} {x y : SurrealHahnSeries}
    (_ : x.length < o) (_ : y.length < o) : Numeric x ∧ Numeric y ∧
      (x < y → toIGame x < toIGame y) := by
  have hx' := numeric_toIGame' x toIGame_aux
  have hy' := numeric_toIGame' y toIGame_aux
  have IHx (z) (hz : length z < x.length) : Numeric z := (toIGame_aux hz hz).1
  have IHy (z) (hz : length z < y.length) : Numeric z := (toIGame_aux hz hz).1
  refine ⟨hx', hy', fun h ↦ ?_⟩
  obtain ⟨i, hi, hi'⟩ := lt_def.1 h
  dsimp at *
  obtain hx | hx := eq_or_ne (x.coeff i) 0 <;> obtain hy | hy := eq_or_ne (y.coeff i) 0
  · simp_all
  · by_cases! H : ∀ j : x.support, i < j
    · apply toIGame_lt_toIGame_of_truncLT _ IHy
      rw [truncLT_def]
      use i, hy, x.coeff i, hi'
      ext j
      have (hj : j < i) : x.coeff j = 0 := by
        by_contra hj'
        exact (H ⟨_, hj'⟩).not_gt hj
      have := lt_trichotomy i j
      aesop
    · obtain ⟨⟨j, hj⟩, (hj' : j ≤ i), hij⟩ := wellFounded_gt.has_min {j : x.support | j ≤ i} H
      obtain rfl | hj' := hj'.eq_or_lt
      · cases hj hx
      · obtain ⟨r, hr⟩ := exists_gt (x.coeff j)
        trans ↑(x.trunc j + single j r)
        · apply toIGame_lt_toIGame_of_truncGT _ IHx
          rw [truncGT_def]
          use j, hj, r
        · rw [hx] at hi'
          obtain ⟨s, hs, hs'⟩ := exists_between hi'
          trans ↑(y.trunc i + single i s)
          · grw [toIGame_succ_equiv (by simp), toIGame_succ (by simp) hs.ne']
            apply add_lt_add_of_le_of_lt (le_of_eq _)
            · apply Numeric.mul_wpow_lt_mul_wpow_of_pos _ hs
              simpa [← Surreal.mk_lt_mk]
            · congr 1
              trans x.trunc i
              · refine trunc_eq_trunc hj'.le fun k hj hi ↦ ?_
                by_contra h
                exact hij ⟨_, h⟩ hi hj
              · aesop
          · apply toIGame_lt_toIGame_of_truncLT _ IHy
            rw [truncLT_def]
            use i, hy, s
  -- TODO: can we more immediately prove this case from the previous?
  · by_cases! H : ∀ j : y.support, i < j
    · apply toIGame_lt_toIGame_of_truncGT _ IHx
      rw [truncGT_def]
      use i, hx, y.coeff i, hi'
      ext j
      have (hj : j < i) : y.coeff j = 0 := by
        by_contra hj'
        exact (H ⟨_, hj'⟩).not_gt hj
      have := lt_trichotomy i j
      aesop
    · obtain ⟨⟨j, hj⟩, (hj' : j ≤ i), hij⟩ := wellFounded_gt.has_min {j : y.support | j ≤ i} H
      obtain rfl | hj' := hj'.eq_or_lt
      · cases hj hy
      · obtain ⟨r, hr⟩ := exists_lt (y.coeff j)
        trans ↑(y.trunc j + single j r)
        · rw [hy] at hi'
          obtain ⟨s, hs', hs⟩ := exists_between hi'
          trans ↑(x.trunc i + single i s)
          · apply toIGame_lt_toIGame_of_truncGT _ IHx
            rw [truncGT_def]
            use i, hx, s
          · grw [toIGame_succ (by simp) hs.ne, toIGame_succ_equiv (by simp)]
            apply add_lt_add_of_le_of_lt (le_of_eq _)
            · apply Numeric.mul_wpow_lt_mul_wpow_of_neg _ hs
              simpa [← Surreal.mk_lt_mk]
            · congr 1
              trans y.trunc i
              · aesop
              · symm
                refine trunc_eq_trunc hj'.le fun k hj hi ↦ ?_
                by_contra h
                exact hij ⟨_, h⟩ hi hj
        · apply toIGame_lt_toIGame_of_truncLT _ IHy
          rw [truncLT_def]
          use j, hj, r
  · obtain ⟨r, hr, hr'⟩ := exists_between hi'
    trans ↑(x.trunc i + single i r)
    · apply toIGame_lt_toIGame_of_truncGT _ IHx
      rw [truncGT_def]
      use i, hx, r
    · apply toIGame_lt_toIGame_of_truncLT _ IHy
      rw [truncLT_def]
      use i, hy, r, hr'
      aesop
termination_by o

instance numeric_toIGame (x : SurrealHahnSeries) : Numeric (toIGame x) :=
  (toIGame_aux (lt_add_one _) (lt_add_one _)).1

theorem toIGame_strictMono : StrictMono toIGame := by
  refine fun x y h ↦ (toIGame_aux (o := max (x.length + 1) (y.length + 1)) ?_ ?_).2.2 h <;> simp

@[simp, norm_cast]
theorem toIGame_lt_toIGame_iff {x y : SurrealHahnSeries} : toIGame x < toIGame y ↔ x < y :=
  toIGame_strictMono.lt_iff_lt

@[simp, norm_cast]
theorem toIGame_le_toIGame_iff {x y : SurrealHahnSeries} : toIGame x ≤ toIGame y ↔ x ≤ y :=
  toIGame_strictMono.le_iff_le

@[simp, norm_cast]
theorem toIGame_equiv_toIGame_iff {x y : SurrealHahnSeries} : toIGame x ≈ toIGame y ↔ x = y := by
  simp [AntisymmRel, le_antisymm_iff]

@[simp, norm_cast]
theorem toIGame_inj {x y : SurrealHahnSeries} : toIGame x = toIGame y ↔ x = y :=
  toIGame_strictMono.injective.eq_iff

theorem toIGame_equiv (x : SurrealHahnSeries) :
    toIGame x ≈ !{toIGame '' truncLT x | toIGame '' truncGT x} := by
  induction x using lengthRecOn with
  | succ x i r hi hr IH =>
    have hi' : i ∉ x.support := fun hi' ↦ (hi i hi').false
    apply Fits.equiv_of_forall_moves_of_equiv (
      !{toIGame '' truncLT x | toIGame '' truncGT x} +
      !{(fun s : ℝ ↦ s * ω^ i.out) '' Iio r | (fun s : ℝ ↦ s * ω^ i.out) '' Ioi r})
    · grw [toIGame_succ hi hr, Numeric.realCast_mul_wpow_equiv, IH]
    · constructor
      all_goals
        rw [moves_ofSets, forall_mem_image]
        intro y hy
      · simpa using lt_of_truncLT hy
      · simpa using gt_of_truncGT hy
    · simp_rw [forall_moves_add, moves_ofSets, Player.cases,
        forall_mem_image, exists_mem_image, forall_mem_truncLT, exists_mem_truncLT, trunc_add]
      constructor
      · intro j hj s hs
        obtain ⟨t, ht⟩ := exists_lt ((x + single i r).coeff i)
        refine ⟨i, ?_, t, ht, ?_⟩
        · simp_all
        · grw [← Numeric.realCast_mul_wpow_equiv, trunc_single_of_le le_rfl,
            ← toIGame_succ_equiv (by aesop), toIGame_le_toIGame_iff]
          refine (lt_def.2 ⟨j, fun k hk ↦ ?_, ?_⟩).le
          · dsimp
            rw [coeff_trunc_of_lt hk, coeff_trunc_of_lt ((hi _ hj).trans hk)]
            aesop
          · aesop
      · intro s hs
        obtain ⟨t, ht, ht'⟩ := exists_between (α := ℝ) hs
        refine ⟨i, ?_, t, ?_, ?_⟩
        · simp_all
        · simp_all
        · grw [trunc_single_of_le le_rfl, ← IH, toIGame_succ_equiv (by simp), trunc_eq_self hi]
          simpa using ht.le
    -- TODO: can we more immediately prove this case from the previous?
    · simp_rw [forall_moves_add, moves_ofSets, Player.cases,
        forall_mem_image, exists_mem_image, forall_mem_truncGT, exists_mem_truncGT, trunc_add]
      constructor
      · intro j hj s hs
        obtain ⟨t, ht⟩ := exists_gt ((x + single i r).coeff i)
        refine ⟨i, ?_, t, ht, ?_⟩
        · simp_all
        · grw [← Numeric.realCast_mul_wpow_equiv, trunc_single_of_le le_rfl,
            ← toIGame_succ_equiv (by aesop), toIGame_le_toIGame_iff]
          refine (lt_def.2 ⟨j, fun k hk ↦ ?_, ?_⟩).le
          · dsimp
            rw [coeff_trunc_of_lt hk, coeff_trunc_of_lt ((hi _ hj).trans hk)]
            aesop
          · aesop
      · intro s hs
        obtain ⟨t, ht, ht'⟩ := exists_between (α := ℝ) hs
        refine ⟨i, ?_, t, ?_, ?_⟩
        · simp_all
        · simp_all
        · grw [trunc_single_of_le le_rfl, ← IH, toIGame_succ_equiv (by simp), trunc_eq_self hi]
          simpa using ht'.le
  | limit x hx IH => rw [toIGame_limit hx]

instance numeric_ofSets_truncLT_truncGT (x : SurrealHahnSeries) :
    Numeric !{toIGame '' truncLT x | toIGame '' truncGT x} := by
  rw [numeric_def]
  constructor
  · simp_rw [moves_ofSets, Player.cases, forall_mem_image]
    intro i hi j hj
    exact_mod_cast (lt_of_truncLT hi).trans (gt_of_truncGT hj)
  · simp [numeric_toIGame]

theorem fits_ofSets_truncLT_truncGT (x : SurrealHahnSeries) (i : Ordinal) :
    (toIGame x).Fits
      !{toIGame '' (x.truncIdx i).truncLT | toIGame '' (x.truncIdx i).truncGT} := by
  constructor
  all_goals
    intro k hk
    rw [moves_ofSets] at hk
    obtain ⟨k, hk, rfl⟩ := hk
    rw [toIGame_le_toIGame_iff, not_le]
  exacts [lt_of_truncLT (truncLT_truncIdx_subset hk), gt_of_truncGT (truncGT_truncIdx_subset hk)]

/-- The surreal that corresponds to a given surreal Hahn series. -/
@[coe]
def toSurreal (x : SurrealHahnSeries) : Surreal :=
  .mk x

@[simp]
theorem mk_toIGame (x : SurrealHahnSeries) : Surreal.mk x.toIGame = toSurreal x :=
  rfl

instance : Coe SurrealHahnSeries Surreal where
  coe := toSurreal

theorem toSurreal_strictMono : StrictMono toSurreal :=
  toIGame_strictMono

@[simp, norm_cast]
theorem toSurreal_lt_toSurreal_iff {x y : SurrealHahnSeries} : toSurreal x < toSurreal y ↔ x < y :=
  toIGame_lt_toIGame_iff

@[simp, norm_cast]
theorem toSurreal_le_toSurreal_iff {x y : SurrealHahnSeries} : toSurreal x ≤ toSurreal y ↔ x ≤ y :=
  toIGame_le_toIGame_iff

@[simp, norm_cast]
theorem toSurreal_inj {x y : SurrealHahnSeries} : toSurreal x = toSurreal y ↔ x = y :=
  toSurreal_strictMono.injective.eq_iff

@[simp]
theorem toSurreal_zero : toSurreal 0 = 0 := by simp [toSurreal]

theorem toSurreal_eq' {x : SurrealHahnSeries.{u}} :
    toSurreal x = .mk !{toIGame '' truncLT x | toIGame '' truncGT x} :=
  Surreal.mk_eq <| toIGame_equiv x

theorem toSurreal_eq {x : SurrealHahnSeries.{u}} :
    toSurreal x = !{toSurreal '' truncLT x | toSurreal '' truncGT x}'(by
      rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
      exact_mod_cast (lt_of_truncLT hi).trans (gt_of_truncGT hj)
    ) := by
  rw [toSurreal_eq', Surreal.mk_ofSets]
  congr <;> aesop

theorem birthday_truncIdx_le (x : SurrealHahnSeries) (i : Ordinal) :
    Surreal.birthday (x.truncIdx i) ≤ Surreal.birthday x := by
  conv_lhs => rw [toSurreal_eq']
  exact (fits_ofSets_truncLT_truncGT ..).birthday_le

theorem birthday_truncIdx_lt {x : SurrealHahnSeries} {i : Ordinal} (h : i < x.length) :
    Surreal.birthday (x.truncIdx i) < Surreal.birthday x := by
  conv_lhs => rw [toSurreal_eq']
  apply (fits_ofSets_truncLT_truncGT ..).birthday_lt
  grw [← toIGame_equiv, toIGame_equiv_toIGame_iff]
  exact (truncIdx_ne h).symm

theorem birthday_truncIdx_monotone (x : SurrealHahnSeries) :
    Monotone fun i ↦ Surreal.birthday (truncIdx x i) := by
  intro i j h
  convert birthday_truncIdx_le (x.truncIdx j) i using 3
  rw [truncIdx_truncIdx, min_eq_right h]

theorem birthday_truncIdx_strictMonoOn (x : SurrealHahnSeries) :
    StrictMonoOn (fun i ↦ Surreal.birthday (truncIdx x i)) (Iio x.length) := by
  intro i hi j hj h
  convert birthday_truncIdx_lt (x := x.truncIdx j) (i := i) _ using 3
  · rw [truncIdx_truncIdx, min_eq_right h.le]
  · simp_all

end SurrealHahnSeries

/-! ### Surreals as Hahn series -/

namespace Surreal

/-- An auxiliary type containing the truncations of `x.toSurrealHahnSeries`.

We'll show that this type, ordered by length, forms a complete linear order, whose supremum
satisfies `toSurreal ⊤ = x`. -/
@[ext]
structure PartialSum (x : Surreal) : Type _ where
  /-- The underlying `SurrealHahnSeries`. -/
  carrier : SurrealHahnSeries
  /-- Every non-zero coefficient matches that of `x.toSurrealHahnSeries`. -/
  coeffIdx_eq_leadingCoeff_sub {i} (hi : i < carrier.length) :
    carrier.coeffIdx i = (x - carrier.truncIdx i).leadingCoeff
  /-- Every non-zero exponent matches that of `x.toSurrealHahnSeries`. -/
  exp_eq_wlog_sub {i} (hi : i < carrier.length) :
    carrier.exp ⟨i, hi⟩ = (x - carrier.truncIdx i).wlog

namespace PartialSum
variable {x : Surreal.{u}}

open SurrealHahnSeries

instance : Bot (PartialSum x) where
  bot := ⟨0, by simp, by simp⟩

theorem carrier_injective : Function.Injective (carrier (x := x)) := by
  intro i j h
  ext
  rw [h]

@[simp]
theorem carrier_inj {y z : PartialSum x} : y.carrier = z.carrier ↔ y = z :=
  carrier_injective.eq_iff

@[simp]
theorem carrier_bot : carrier (⊥ : PartialSum x) = 0 :=
  rfl

/-- The length of the carrier. -/
def length (y : PartialSum x) : Ordinal :=
  y.carrier.length

@[simp]
theorem length_bot : length (⊥ : PartialSum x) = 0 := by
  simp [length]

instance : Preorder (PartialSum x) :=
  .lift length

instance : WellFoundedLT (PartialSum x) where
  wf := InvImage.wf length wellFounded_lt

instance : WellFoundedRelation (PartialSum x) :=
  ⟨_, wellFounded_lt⟩

theorem length_strictMono : StrictMono (length (x := x)) :=
  fun _ _ ↦ id

@[simp] theorem length_lt_length {y z : PartialSum x} : length y < length z ↔ y < z := .rfl
@[simp] theorem length_le_length {y z : PartialSum x} : length y ≤ length z ↔ y ≤ z := .rfl

/-- Truncating the series preserves that it is an initial segment. -/
def truncIdx (y : PartialSum x) (i : Ordinal) : PartialSum x where
  carrier := y.carrier.truncIdx i
  coeffIdx_eq_leadingCoeff_sub {j} hj := by
    have hj' : j < i := hj.trans_le (by simp)
    rw [coeffIdx_truncIdx_of_lt hj', truncIdx_truncIdx, min_eq_right hj'.le]
    apply y.coeffIdx_eq_leadingCoeff_sub (hj.trans_le _)
    simp
  exp_eq_wlog_sub {j} hj := by
    have hj' : j < i := hj.trans_le (by simp)
    rw [exp_truncIdx, truncIdx_truncIdx, min_eq_right hj'.le, y.exp_eq_wlog_sub]

@[simp]
theorem carrier_truncIdx (y : PartialSum x) (i : Ordinal) :
    (y.truncIdx i).carrier = y.carrier.truncIdx i :=
  rfl

@[simp, grind =]
theorem length_truncIdx (y : PartialSum x) (i : Ordinal) : (y.truncIdx i).length = min i y.length :=
  y.carrier.length_truncIdx i

theorem truncIdx_le (y : PartialSum x) (i : Ordinal) : y.truncIdx i ≤ y :=
  (length_truncIdx ..).trans_le (min_le_right ..)

@[simp]
theorem truncIdx_truncIdx (y : PartialSum x) (i j : Ordinal) :
    (y.truncIdx i).truncIdx j = y.truncIdx (min i j) :=
  carrier_injective <| SurrealHahnSeries.truncIdx_truncIdx ..

@[simp]
theorem truncIdx_length (y : PartialSum x) : y.truncIdx y.length = y := by
  apply carrier_injective
  rw [carrier_truncIdx, truncIdx_of_le]
  rfl

theorem truncIdx_length_of_le {y z : PartialSum x} (h : y ≤ z) : z.truncIdx y.length = y := by
  have IH {i} (hi : i < y.length) : (z.truncIdx y.length).truncIdx i = y.truncIdx i := by
    have : y.truncIdx i < y := by
      rw [← length_lt_length, length_truncIdx]
      simpa
    convert truncIdx_length_of_le (y := y.truncIdx i) (z := z) _ using 1
    · simp [min_comm]
    · exact (truncIdx_le y i).trans h
  apply carrier_injective (exp_ext _ _ _)
  · exact (length_truncIdx ..).trans (min_eq_left h)
  · intro i hx hy
    rw [exp_eq_wlog_sub, exp_eq_wlog_sub]
    congr 3
    rw [← carrier_truncIdx, ← carrier_truncIdx, carrier_inj, IH hy]
  · intro i hx hy
    rw [coeffIdx_eq_leadingCoeff_sub _ hx, coeffIdx_eq_leadingCoeff_sub _ hy]
    congr 3
    rw [← carrier_truncIdx, ← carrier_truncIdx, carrier_inj, IH hy]
termination_by y

theorem length_injective : Function.Injective (length (x := x)) := by
  intro y z h
  rw [← truncIdx_length_of_le h.le, h, truncIdx_length]

@[simp]
theorem length_inj {y z : PartialSum x} : length y = length z ↔ y = z :=
  length_injective.eq_iff

instance : LinearOrder (PartialSum x) where
  le_antisymm y z h₁ h₂ := by
    rw [← length_inj]
    exact h₁.antisymm h₂
  le_total y z := le_total y.length z.length
  toDecidableLE := Classical.decRel _

theorem exp_congr {y z : PartialSum x} (i : Iio y.carrier.length) (j : Iio z.carrier.length)
    (h : i.1 = j.1) : (y.carrier.exp i).1 = (z.carrier.exp j).1 := by
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  subst h
  obtain hyz | hyz := le_total y z
  all_goals
    rw [SurrealHahnSeries.exp_congr (carrier_inj.2 (truncIdx_length_of_le hyz)).symm,
      SurrealHahnSeries.exp_congr (carrier_truncIdx ..)]
    simp

theorem exp_lt_exp {y z : PartialSum x} {i : Iio y.carrier.length} {j : Iio z.carrier.length}
    (h : i.1 < j.1) : (z.carrier.exp j).1 < (y.carrier.exp i).1 := by
  obtain hyz | hyz := le_total y z
  all_goals
    rw [SurrealHahnSeries.exp_congr (carrier_inj.2 (truncIdx_length_of_le hyz).symm),
      SurrealHahnSeries.exp_congr (carrier_truncIdx ..), exp_truncIdx]
    simpa

theorem coeffIdx_congr {y z : PartialSum x} {i : Ordinal} (hy : i < y.length) (hz : i < z.length) :
    coeffIdx y.carrier i = coeffIdx z.carrier i := by
  obtain hyz | hyz := le_total y z <;>
    rwa [← truncIdx_length_of_le hyz, carrier_truncIdx, coeffIdx_truncIdx_of_lt]

theorem birthday_strictMono : StrictMono fun y : PartialSum x ↦ birthday y.carrier := by
  intro y z h
  dsimp
  rw [← truncIdx_length_of_le h.le]
  exact birthday_truncIdx_lt h

theorem birthday_le (y : PartialSum x) : birthday y.carrier ≤ birthday x := by
  cases x with | mk z
  rw [toSurreal_eq']
  apply Fits.birthday_le
  unfold truncLT truncGT
  constructor
  all_goals
    rw [moves_ofSets, forall_mem_image, forall_mem_truncAux]
    intro i hi r hr
    grw [Numeric.not_le, toIGame_succ_equiv (by simp), add_comm]
    first | rw [← IGame.lt_sub_iff_add_lt] | rw [← IGame.sub_lt_iff_lt_add]
    rw [← Surreal.mk_lt_mk]
    apply leadingTerm_mono.reflect_lt
    simp
    obtain ⟨⟨i, hi'⟩, rfl⟩ := eq_exp_of_mem_support hi
    rw [leadingTerm, trunc_exp, ← coeffIdx_eq_leadingCoeff_sub _ hi', ← exp_eq_wlog_sub _ hi']
    simpa using hr

instance : Small.{u} (PartialSum x) := by
  refine small_of_injective (β := Iic x.birthday) (f := fun y ↦ ⟨_, birthday_le y⟩) fun y z h ↦
    birthday_strictMono.injective ?_
  simpa using h

/-- The function used in `sSup`. -/
private def sSupFun (s : Set (PartialSum x)) (i : Iio (⨆ x : s, x.1.length)) : Surreal × ℝ :=
  have H := (lt_ciSup_iff' (Ordinal.bddAbove_of_small _)).1 i.2
  ⟨exp _ ⟨_, Classical.choose_spec H⟩, coeffIdx (Classical.choose H).1.1 i⟩

private theorem sSupFun_ne_zero {s : Set (PartialSum x)} (i : Iio (⨆ x : s, x.1.length)) :
    (sSupFun s i).2 ≠ 0 := by
  dsimp [sSupFun]
  generalize_proofs H
  rw [coeffIdx_eq_zero_iff, not_le]
  exact Classical.choose_spec H

/-- The Hahn series corresponding to `sSup`. -/
private def sSupAux (s : Set (PartialSum x)) : SurrealHahnSeries :=
  .ofSeq (⨆ x : s, x.1.length) (sSupFun s) fun _ _ h ↦ exp_lt_exp h

private theorem length_sSupAux (s : Set (PartialSum x)) :
    (sSupAux s).length = ⨆ x : s, x.1.length :=
  length_ofSeq sSupFun_ne_zero

private theorem coeffIdx_sSupAux {s : Set (PartialSum x)} {y : PartialSum x}
    {i : Ordinal} (hs : i < (sSupAux s).length) (hi : i < y.length) :
    coeffIdx (sSupAux s) i = coeffIdx y.carrier i := by
  unfold sSupAux sSupFun
  generalize_proofs _ H _
  rw [coeffIdx_ofSeq _ (length_sSupAux s ▸ hs), coeffIdx_congr]
  exacts [hi, H _ _, sSupFun_ne_zero]

private theorem exp_sSupAux {s : Set (PartialSum x)} {y : PartialSum x}
    {i : Ordinal} (hs : i < (sSupAux s).length) (hy : i < y.length) :
    ((sSupAux s).exp ⟨i, hs⟩).1 = y.carrier.exp ⟨i, hy⟩ := by
  dsimp [sSupAux]
  generalize_proofs _ H _
  rw [exp_ofSeq _ sSupFun_ne_zero]
  apply exp_congr
  rfl

private theorem truncIdx_sSupAux {s : Set (PartialSum x)} {y : PartialSum x}
    {i : Ordinal} (hs : i < (sSupAux s).length) (hy : i < y.length) :
    (sSupAux s).truncIdx i = y.carrier.truncIdx i := by
  refine exp_ext ?_ (fun j hj hj' ↦ ?_) (fun j hj hj' ↦ ?_)
  · aesop
  · rw [exp_truncIdx, exp_sSupAux (y := y.truncIdx i)]
    · simp
    · grind
  · rw [coeffIdx_truncIdx_of_lt, ← carrier_truncIdx]
    · apply coeffIdx_sSupAux <;> grind
    · grind

-- Directed union
instance : SupSet (PartialSum x) where
  sSup s := by
    refine ⟨sSupAux s, ?_, ?_⟩
    all_goals
      intro i hi
      have hi' := length_sSupAux _ ▸ hi
      rw [lt_ciSup_iff' (Ordinal.bddAbove_of_small _)] at hi'
      obtain ⟨⟨y, hy⟩, hy'⟩ := hi'
    · rw [coeffIdx_sSupAux hi hy', coeffIdx_eq_leadingCoeff_sub _ hy', truncIdx_sSupAux hi hy']
    · rw [exp_sSupAux hi hy', exp_eq_wlog_sub _ hy', truncIdx_sSupAux hi hy']

@[simp]
theorem length_sSup (s : Set (PartialSum x)) : (sSup s).length = ⨆ x : s, x.1.length :=
  length_sSupAux s

instance : CompleteSemilatticeSup (PartialSum x) where
  le_sSup s y hy := by
    rw [← length_le_length, length_sSup]
    exact le_ciSup (Ordinal.bddAbove_of_small _) (⟨y, hy⟩ : s)
  sSup_le s y := by
    rw [← length_le_length, length_sSup, ciSup_le_iff' (Ordinal.bddAbove_of_small _)]
    simp

instance : CompleteLattice (PartialSum x) :=
  completeLatticeOfCompleteSemilatticeSup _

instance : CompleteLinearOrder (PartialSum x) where
  __ := LinearOrder.toBiheytingAlgebra _
  __ := instCompleteLattice
  __ := instLinearOrder

theorem mk_sub_wlog_strictMono :
    StrictMono fun y : PartialSum x ↦ ArchimedeanClass.mk (x - y.carrier) := by
  intro y z h
  dsimp

  #exit

def succ (y : PartialSum x) : PartialSum x where
  carrier := y.carrier + single (x - y.carrier).wlog (x - y.carrier).leadingCoeff
  coeffIdx_eq_leadingCoeff_sub {i} hi := by
    sorry
  exp_eq_wlog_sub := sorry

theorem length_succ_of_ne {y : PartialSum x} (h : x ≠ y.carrier) :
    (succ y).length = y.length + 1 := by
  sorry

theorem toSurreal_top : (⊤ : PartialSum x).carrier = x := by
  by_contra! h
  apply (le_top (a := succ ⊤)).not_gt
  rw [← length_lt_length, length_succ_of_ne h.symm, Order.lt_add_one_iff]

end PartialSum

/-- The **Conway normal form** of a surreal number. -/
@[coe]
def toSurrealHahnSeries (x : Surreal) : SurrealHahnSeries :=
  (⊤ : PartialSum x).carrier

@[simp]
theorem toSurreal_toSurrealHahnSeries (x : Surreal) : x.toSurrealHahnSeries = x :=
  PartialSum.toSurreal_top

end Surreal
