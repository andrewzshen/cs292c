/-
  # EXERCISES FOR `L02`

  Some of the exercises are adapted from "Theorem Proving in Lean" and Velleman's "How to Prove It"

  ## INSTRUCTIONS

  Replace the `sorry` in each exercise with a proof of the given proposition.
-/

import Course.CourseLib

variable (P Q R : Prop)

theorem or_assoc_fwd (h : (P ∨ Q) ∨ R) : P ∨ (Q ∨ R) := by
  cases h with                                                                                                          
  | inl hPQ =>
    cases hPQ with 
    | inl hP => left; exact hP
    | inr hQ => right; left; exact hQ
  | inr hR => right; right; exact hR

theorem or_assoc_bwd (h : P ∨ (Q ∨ R)) : (P ∨ Q) ∨ R := by
  cases h with
  | inl hP => left; left; exact hP 
  | inr hQR => 
    cases hQR with    
    | inl hQ => left; right; exact hQ
    | inr hR => right; exact hR

theorem ex1_1 : (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R) := by
  constructor
  · exact or_assoc_fwd P Q R
  · exact or_assoc_bwd P Q R

theorem and_distrib_fwd (h : P ∧ (Q \or R)) : (P \and Q) \or (P \and R) := by


theorem ex1_2 : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  sorry

theorem ex1_3 : (P → (Q → R)) ↔ (P ∧ Q → R) := by
  sorry

theorem ex1_4 : ((P ∨ Q) → R) ↔ (P → R) ∧ (Q → R) := by
  sorry

theorem ex1_5 : ¬P ∨ ¬Q → ¬(P ∧ Q) := by
  sorry

theorem ex1_6 : ¬P → (P → Q) := by
  sorry
