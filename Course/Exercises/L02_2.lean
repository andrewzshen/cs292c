/-
  # EXERCISES FOR `L02`

  Some of the exercises are adapted from "Theorem Proving in Lean" and Velleman's "How to Prove It"

  ## INSTRUCTIONS

  Replace the `sorry` in each exercise with a proof of the given proposition.
-/

import Course.CourseLib

variable {α : Type} (A B C : Set α) (x : α)

theorem ex2_1 : x ∈ A \ (A ∩ B) ↔ x ∈ A \ B := by
  constructor
  · intro h
    constructor
    · exact h.1
    · intro hxB
      exact h.2 ⟨h.1, hxB⟩ 
  · intro h
    constructor
    · exact h.1
    · intro hxAB
      exact h.2 hxAB.2

theorem ex2_2 : x ∈ A ∪ (B ∩ C) ↔ x ∈ (A ∪ B) ∩ (A ∪ C) := by
  constructor
  · intro h
    obtain hxA | ⟨hxB, hxC⟩ := h 
    · constructor
      · left
        exact hxA
      · left
        exact hxA
    · constructor
      · right
        exact hxB
      · right
        exact hxC
  · intro h
    obtain ⟨hxAB, hxAC⟩ := h 
    obtain hxA | hxB := hxAB 
    · left
      exact hxA
    · obtain hxA | hxC := hxAC 
      · left
        exact hxA
      · right
        exact ⟨hxB, hxC⟩

theorem ex2_3 : x ∈ (A ∪ B) \ C ↔ x ∈ (A \ C) ∪ (B \ C) := by
  constructor
  · intro h
    obtain ⟨hxA | hxB, hxnC⟩ := h   
    · left
      exact ⟨hxA, hxnC⟩ 
    · right 
      exact ⟨hxB, hxnC⟩ 
  · intro h
    obtain ⟨hxA, hxnC⟩ | ⟨hxB, hxnC⟩ := h   
    · exact ⟨Or.inl hxA, hxnC⟩     
    · exact ⟨Or.inr hxB, hxnC⟩     

/-
  HINT: depending on how you do the proof, you may find one or more of the
  theorems in `L02_BasicProofs::USEFUL_THEOREMS` to be...well, useful -/
theorem ex2_4 : x ∈ A ∪ (B \ C) ↔ x ∈ (A ∪ B) \ (C \ A) := by
  constructor
  · intro h
    obtain hxA | ⟨hxB, hxnC⟩ := h  
    · constructor
      · left
        exact hxA
      · intro hxCA
        exact hxCA.2 hxA 
    · constructor 
      · right
        exact hxB
      · intro hxCA 
        exact hxnC hxCA.1 
  · intro h
    obtain ⟨hxA | hxB, hxnCA⟩ := h 
    · left
      exact hxA
    · by_cases hxA : x ∈ A 
      · left
        exact hxA 
      · right
        refine ⟨hxB, ?_⟩
        intro hxC
        exact hxnCA ⟨hxC, hxA⟩  
