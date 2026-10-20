/-
  # EXERCISES FOR `L05`
-/

import Course.CourseLib

/-
  ## INSTRUCTIONS

  Prove that `qsort` terminates by filling in the `sorry` in the lemmas below
-/

/-
  HINT: some potentially helpful theorems -/
#check List.partition_eq_filter_filter
#check List.length_filter_le

lemma qsort_term1
  (x : ℕ) (xs : List ℕ)
  : (List.partition (· ≤ x) xs).1.length < (x :: xs).length
:= by
  simp only [List.partition_eq_filter_filter, List.length_cons]
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem qsort_term2
  (x : ℕ) (xs : List ℕ)
  : (List.partition (· ≤ x) xs).2.length < (x :: xs).length
:= by
  simp only [List.partition_eq_filter_filter, List.length_cons]
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

def qsort : List ℕ → List ℕ
  | [] => []
  | x :: xs =>
    let ℓs := xs.partition (· ≤ x)
    qsort ℓs.1 ++ [x] ++ qsort ℓs.2
termination_by ℓ => ℓ.length
decreasing_by
  · exact qsort_term1 x xs
  · exact qsort_term2 x xs
