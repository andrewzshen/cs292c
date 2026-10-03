/-
  # EXERCISES FOR `L02`

  Some of the exercises are adapted from "Theorem Proving in Lean" and Velleman's "How to Prove It"

  ## INSTRUCTIONS

  Replace the `sorry` in each exercise with a proof of the given proposition.
-/

import Course.CourseLib

abbrev even (n : ℕ) :=
  ∃ (k : ℕ), n = 2 * k

abbrev odd (n : ℕ) :=
  ∃ (k : ℕ), n = 2 * k + 1

theorem ex6_1 : ∀ n, even n ∨ odd n := by
  intro n
  induction n with
  | zero => 
    left
    exists 0
  | succ n ih =>
    cases ih with
    | inl h_even =>
      right
      obtain ⟨k, hk⟩ := h_even
      exists k
      rw [hk]
    | inr h_odd =>
      left 
      obtain ⟨k, hk⟩ := h_odd
      exists k + 1
      rw [hk]
      linarith

/-
  HINT: you may find the following two theorems useful for `ex6_2`. Given a
  proof that a proposition is true or false, they can be used to reduce an `if`
  expression into the true or false branches. Ignore the `@` when using the
  theorem, it's only there to make the `#check` output look nicer. -/
#check @if_pos
#check @if_neg

/- Factorial function -/
def fact (n : ℕ) :=
  if n = 0 then 1
  else n * fact (n-1)

theorem ex6_2 : ∀ (n : Nat), fact n ≥ 1 := by
  intro n
  induction n with
  | zero =>
    unfold fact
    rw [if_pos] 
    rfl
  | succ n ih =>
    unfold fact
    have h_ne : n + 1 ≠ 0 := Nat.succ_ne_zero n 
    rw [if_neg h_ne]
    have h_sub : n + 1 - 1 = n := rfl
    rw [h_sub]
    nlinarith
 
