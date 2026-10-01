/-
  # EXERCISES FOR `L02`

  Some of the exercises are adapted from "Theorem Proving in Lean" and Velleman's "How to Prove It"

  ## INSTRUCTIONS

  Replace the `sorry` in each exercise with a proof of the given proposition.
-/

import Course.CourseLib

variable (P Q R : Prop)

theorem ex1_1 : (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R) := by
  constructor
  · intro h -- Forward direction 
    cases h with                                                                                                          
    | inl hPQ =>
      cases hPQ with 
      | inl hP => left; exact hP
      | inr hQ => right; left; exact hQ
    | inr hR => right; right; exact hR
  · intro h -- Backward direction 
    cases h with
    | inl hP => left; left; exact hP 
    | inr hQR => 
      cases hQR with    
      | inl hQ => left; right; exact hQ
      | inr hR => right; exact hR

theorem ex1_2 : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  constructor
  · intro h -- Forward direction
    obtain ⟨hP, hQR⟩ := h
    cases hQR with
    | inl hQ => left;  exact ⟨hP, hQ⟩  
    | inr hR => right; exact ⟨hP, hR⟩  
  · intro h -- Backward direction
    cases h with
    | inl hPQ =>
      obtain ⟨hP, hQ⟩ := hPQ 
      constructor
      · exact hP
      · left; exact hQ
    | inr hPR =>
      obtain ⟨hP, hR⟩ := hPR 
      constructor
      · exact hP
      · right; exact hR

theorem ex1_3 : (P → (Q → R)) ↔ (P ∧ Q → R) := by
  constructor
  · intro h hPQ -- Forward direction
    obtain ⟨hP, hQ⟩ := hPQ
    exact h hP hQ
  · intro h hP hQ -- Backward direction
    exact h ⟨hP, hQ⟩

theorem ex1_4 : ((P ∨ Q) → R) ↔ (P → R) ∧ (Q → R) := by
  constructor
  · intro h -- Forward direction
    constructor
    · intro hP
      exact h (Or.inl hP) 
    · intro hQ
      exact h (Or.inr hQ) 
  · intro h hPQ -- Backward direction
    obtain ⟨hPR, hQR⟩:= h
    cases hPQ with
    | inl hP => exact hPR hP 
    | inr hQ => exact hQR hQ 

theorem ex1_5 : ¬P ∨ ¬Q → ¬(P ∧ Q) := by
  intro h hPQ
  obtain ⟨hP, hQ⟩ := hPQ
  cases h with
  | inl hnP => exact hnP hP 
  | inr hnQ => exact hnQ hQ

theorem ex1_6 : ¬P → (P → Q) := by
  intro hnP hP
  contradiction
  
