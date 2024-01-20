theorem dojo2_uncombined (p : Prop) : p ∨ p → p := by
  intro h
  cases h
  assumption
  assumption

/-
theorem jtest (n : Nat) : n = n := by
  sorry
-/

theorem dojo2_combined (p : Prop) : p ∨ p → p := by
  intro h
  cases h <;> assumption
