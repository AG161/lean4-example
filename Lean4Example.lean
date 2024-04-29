open Nat (add_assoc add_comm)

theorem hello_world (a b c : Nat)
  : a + b + c = a + c + b := by
  rw [add_assoc, add_comm b, ←add_assoc]

theorem dojo1_uncombined (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  exact hp
  apply And.intro
  exact hq
  exact hp

theorem dojo1_combined_term (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp; exact And.intro hq hp

theorem dojo1_combined_tac (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro; exact hp; apply And.intro; exact hq; exact hp

theorem dojo2_uncombined (p : Prop) : p ∨ p → p := by
  intro h
  cases h
  assumption
  assumption

theorem dojo2_combined (p : Prop) : p ∨ p → p := by
  intro h
  cases h <;> assumption

theorem dojo3_uncombined  (x y z : Nat)
        : (x + 0) * (0 + y * 1 + z * 0) = x * y := by
  simp

/- removed for this test
theorem dojo4_uncombined (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  repeat (first | apply And.intro | apply Or.inl; assumption | apply Or.inr | assumption)
-/

theorem localrw (a b c d e f : Nat) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']
  rw [← Nat.mul_assoc]
  rw [h, Nat.mul_assoc]

theorem calc_rw (a b c d : Nat): (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  calc
    (a + b) * (c + d) = a * (c + d) +  b * (c + d)      := by rw [Nat.add_mul a b (c + d)]
    _                 = a * c + a * d + (b * c + b * d) := by rw [Nat.mul_add, Nat.mul_add]
    _                 = a * c + a * d + b * c + b * d   := by rw [Nat.add_assoc ((a * c) + (a * d))]

theorem rw_at (h : a = b) (h₁ : c = b) (h₂ : a = c) : True := by
  rw [h, h₁] at h₂
  trivial

theorem zmul (a : Nat) : 0 * a = 0 := by
  have h : a * 0 = 0 := by
    apply Nat.mul_zero
  rw [Nat.mul_comm]
  exact h

theorem test_have (p q : Prop) : ((p ∧ ¬q) ∨ (q ∧ ¬p)) ↔ ((p ∨ q) ∧ ¬(p ∧ q)) := by
  apply Iff.intro
  · intro h₁
    apply And.intro
    · apply Or.elim h₁
      · exact fun paq => Or.inl paq.1
      · exact fun paq => Or.inr paq.1
    · apply Or.elim h₁
      · exact fun pnq => fun paq => pnq.2 paq.2
      · exact fun qnp => fun paq => qnp.2 paq.1
  · intro h₂
    apply Or.elim h₂.1
    · intro hp
      exact Or.inl (And.intro (hp) (fun hq => h₂.2 (And.intro hp hq)))
    · intro hq
      exact Or.inr (And.intro (hq) (fun hp => h₂.2 (And.intro hp hq)))

theorem test_state (p q : Prop) : ((p ∧ ¬q) ∨ (q ∧ ¬p)) ↔ ((p ∨ q) ∧ ¬(p ∧ q)) := by
  apply Iff.intro
  intro h₁
  apply And.intro
  apply Or.elim h₁
  exact fun paq => Or.inl paq.1
  exact fun paq => Or.inr paq.1
  apply Or.elim h₁
  exact fun pnq => fun paq => pnq.2 paq.2
  exact fun qnp => fun paq => qnp.2 paq.1
  intro h₂
  apply Or.elim h₂.1
  intro hp
  exact Or.inl (And.intro (hp) (fun hq => h₂.2 (And.intro hp hq)))
  intro hq
  exact Or.inr (And.intro (hq) (fun hp => h₂.2 (And.intro hp hq)))

theorem test_have2 (p q : Prop) : ((p ∧ ¬q) ∨ (q ∧ ¬p)) ↔ ((p ∨ q) ∧ ¬(p ∧ q)) := by
  have (h₁ : ((p ∧ ¬q) ∨ (q ∧ ¬p))) : (p ∨ q) ∧ ¬(p ∧ q) := by
    apply And.intro
    · apply Or.elim h₁
      · exact fun paq => Or.inl paq.1
      · exact fun paq => Or.inr paq.1
    · apply Or.elim h₁
      · exact fun pnq => fun paq => pnq.2 paq.2
      · exact fun qnp => fun paq => qnp.2 paq.1
  apply Iff.intro
  · intro h₁
    exact this h₁
  · intro h₂
    apply Or.elim h₂.1
    · intro hp
      exact Or.inl (And.intro (hp) (fun hq => h₂.2 (And.intro hp hq)))
    · intro hq
      exact Or.inr (And.intro (hq) (fun hp => h₂.2 (And.intro hp hq)))

section lem

variable (p q r : Prop)

theorem test_have3 : ((p ∧ ¬q) ∨ (q ∧ ¬p)) ↔ ((p ∨ q) ∧ ¬(p ∧ q)) := by
  have : (h₁ : ((p ∧ ¬q) ∨ (q ∧ ¬p))) → (p ∨ q) ∧ ¬(p ∧ q) := by
    intro h₁
    apply And.intro
    · apply Or.elim h₁
      · exact fun paq => Or.inl paq.1
      · exact fun paq => Or.inr paq.1
    · apply Or.elim h₁
      · exact fun pnq => fun paq => pnq.2 paq.2
      · exact fun qnp => fun paq => qnp.2 paq.1
  apply Iff.intro
  · exact this
  · intro h₂
    apply Or.elim h₂.1
    · intro hp
      exact Or.inl (And.intro (hp) (fun hq => h₂.2 (And.intro hp hq)))
    · intro hq
      exact Or.inr (And.intro (hq) (fun hp => h₂.2 (And.intro hp hq)))

end lem

example : ∃ n : Nat, n * n = 4 := by
  refine ⟨2, ?thing⟩
  rfl

example : ∃ n : Nat, n * n = 4 := by
  refine' ⟨2, _⟩
  rfl
