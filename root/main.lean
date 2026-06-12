import «upper_bound».«main»
import «finite_verify».«main»
import Definitions
theorem root : {n : ℕ | n = digitFactorialSum n} = {1, 2, 145, 40585} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    by_cases hge : n ≥ 10^7
    · have := upper_bound n hge
      omega
    · push_neg at hge
      have hmem : n ∈ {n : ℕ | n ≤ 9999999 ∧ n = digitFactorialSum n} := by
        simp only [Set.mem_setOf_eq]
        exact ⟨by omega, h⟩
      rw [finite_verify] at hmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      exact hmem
  · intro h
    have hmem : n ∈ ({1, 2, 145, 40585} : Set ℕ) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      exact h
    have hsub : ({1, 2, 145, 40585} : Set ℕ) ⊆ {n : ℕ | n ≤ 9999999 ∧ n = digitFactorialSum n} := by
      rw [← finite_verify]
    have := hsub hmem
    simp only [Set.mem_setOf_eq] at this
    exact this.2
