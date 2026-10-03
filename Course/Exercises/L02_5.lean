/-
  # EXERCISES FOR `L02`

  Some of the exercises are adapted from "Theorem Proving in Lean" and Velleman's "How to Prove It"

  ## INSTRUCTIONS

  Replace the `sorry` in each exercise with a proof of the given proposition.
-/

import Course.CourseLib

variable {α β γ : Type} (f : α → β)

def inj       (f : α → β) := ∀ (x y : α), f x = f y → x = y
def surj      (f : α → β) := ∀ (y : β), ∃ (x : α), f x = y
def bijection (f : α → β) := inj f ∧ surj f

/-
  HINT: remember that the `rw` tactic requires an exact match, so rewriting a
  statement into a different form may be necessary (e.g., using
  `Function.comp`) -/

theorem ex5_1
  (f : α → β) (g : β → γ)
  : surj f → surj g → surj (g ∘ f)
:= by
  unfold surj
  intro hf hg z 
  obtain ⟨y, hy⟩ := hg z
  obtain ⟨x, hx⟩ := hf y
  exists x
  rw [Function.comp, hx, hy] 

theorem ex5_2
  (f : α → β) (g : β → α)
  (h : g ∘ f = id)
  : inj f
:= by
  unfold inj 
  intro x y hf
  have hg : g (f x) = g (f y) := by rw [hf]  
  have h₁ : g (f x) = x := by
    have hgf : (g ∘ f) x = id x := by rw [h]
    unfold Function.comp id at hgf
    exact hgf
  have h₂ : g (f y) = y := by
    have hgf : (g ∘ f) y = id y := by rw [h]
    unfold Function.comp id at hgf
    exact hgf
  rw [h₁, h₂] at hg
  exact hg
    
/-
  HINT: the following theorems may be useful for `ex5_3`. Don't forget that
  `nlinarith` can solve some (not all) non-linear arithmetic goals. Ignore the
  `@` when using the theorem, it's only there to make the `#check` output look
  nicer. -/
#check @mul_eq_mul_left_iff
#check @mul_div_cancel₀

theorem ex5_3
  (a b : ℝ) (f : ℝ → ℝ)
  (h1 : f = fun z => a*z + b) (h2 : a ≠ 0)
  : bijection f
:= by
  unfold bijection
  constructor
  · unfold inj 
    intro x y hf
    rw [h1] at hf
    have h3 : a * x = a * y := by linarith
    rw [mul_eq_mul_left_iff] at h3
    cases h3 with
    | inl heq => exact heq 
    | inr ha0 => contradiction
  · unfold surj 
    intro y
    rw [h1]
    exists (y - b) / a
    have h3 : a * ((y - b) / a) = y - b := mul_div_cancel₀ (y - b) h2 
    linarith
