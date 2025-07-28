import Mathlib.Logic.Small.Set
import Mathlib.Logic.Relation
import Mathlib.Order.SetNotation

open Set

universe u

variable {α : Type*} (r : α → α → Prop) [H : ∀ x, Small.{u} {y // r x y}]

private def level [∀ x, Small.{u} {y // r x y}] (x : α) : ℕ → Set α
  | 0 => {x}
  | n + 1 => ⋃₀ ((fun x ↦ {y | r x y}) '' level x n)

private theorem small_level (x : α) : ∀ n, Small.{u} (level r x n)
  | 0 => small_single _
  | n + 1 => by
    refine @small_sUnion _ _ ?_ ?_
    · have := small_level x n
      exact small_image ..
    · simp_all

private theorem small_sUnion_level (x : α) : Small.{u} (⋃₀ range (level r x)) := by
  refine @small_sUnion _ _ ?_ ?_
  · exact small_range ..
  · simp [small_level]

instance small_transGen (x : α) : Small.{u} {y // Relation.TransGen r x y} := by
  refine @small_subset _ _ _ (fun y hy ↦ ?_) (small_sUnion_level r x)
  simp_rw [mem_sUnion, mem_range, exists_exists_eq_and]
  induction hy with
  | single =>
    use 1
    simpa [level]
  | tail hy hr IH =>
    obtain ⟨n, hn⟩ := IH
    use n + 1
    simpa [level] using ⟨_, hn, hr⟩

omit H in
instance small_transGen' [∀ x, Small.{u} {y // r y x}] (x : α) :
    Small.{u} {y // Relation.TransGen r y x} := by
  simp_rw [← Relation.transGen_swap (r := r)]
  exact small_transGen _ x
