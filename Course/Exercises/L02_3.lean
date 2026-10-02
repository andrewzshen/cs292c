/-
  # EXERCISES FOR `L02`

  Some of the exercises are adapted from "Theorem Proving in Lean" and Velleman's "How to Prove It"

  ## INSTRUCTIONS

  Replace the `sorry` in each exercise with a proof of the given proposition.
-/

import Course.CourseLib

variable {α : Type} (P Q : α → Prop) (A B C : Set α)

theorem ex3_1 : (∀ x, P x ∧ Q x) ↔ (∀ x, P x) ∧ (∀ x, Q x) := by
  constructor
  · intro h
    constructor
    · intro x
      exact (h x).1 
    · intro x
      exact (h x).2 
  · intro h
    obtain ⟨hPx, hQx⟩ := h  
    intro x
    constructor
    · exact hPx x
    · exact hQx x

theorem ex3_2 : (∀ x, P x) ∨ (∀ x, Q x) → ∀ x, P x ∨ Q x := by
  intro h
  obtain hPx | hQx := h 
  · intro x
    left
    exact hPx x
  · intro x
    right 
    exact hQx x

theorem ex3_3 : (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) := by
  constructor
  · intro h
    obtain ⟨x, hPx | hQx⟩ := h 
    · left
      exact ⟨x, hPx⟩
    · right 
      exact ⟨x, hQx⟩
  · intro h 
    obtain ⟨x₁, hPx⟩ | ⟨x₂, hQx⟩ := h 
    · exact ⟨x₁, Or.inl hPx⟩  
    · exact ⟨x₂, Or.inr hQx⟩  

theorem ex3_4 : A ⊆ B ↔ A \ B = ∅ := by
  constructor
  · intro h
    ext x 
    constructor
    · intro ⟨hxA, hxnB⟩
      have hxB : x ∈ B := h hxA  
      exact hxnB hxB 
    · intro hx
      exact False.elim hx
  · intro h x hxA 
    by_contra hxnB
    have hxAB : x ∈ A \ B := ⟨hxA, hxnB⟩
    rw [h] at hxAB
    exact hxAB

theorem ex3_5 : C ⊆ A ∪ B ↔ C \ A ⊆ B := by
  constructor 
  · intro h x hxCA
    obtain ⟨hxC, hxnA⟩ := hxCA
    have hxAB : x ∈ A ∪ B := h hxC 
    obtain hxA | hxB := hxAB
    · contradiction
    · exact hxB
  · intro h x hxC
    by_cases hxA : x ∈ A
    · left
      exact hxA
    · right
      have hxCA : x ∈ C \ A := ⟨hxC, hxA⟩ 
      exact h hxCA 
