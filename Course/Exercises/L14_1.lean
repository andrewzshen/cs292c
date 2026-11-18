/-
  # EXERCISES FOR `L14`

  We revisit `L04_1` so that we can redo the proofs using `grind` and `aesop`.
  Annotate as you see fit, and see how much of the proofs you can automate.
  Remember that you can annotate things in other files (e.g., `sorted` and the
  various `sorted` lemmas) using `attribute`.
-/

import Course.CourseLib
import Course.L03_Sorting
import Course.L04_SortingDeux

/-
  Make available the `sorted` predicate and various useful lemmas about the
  `sorted` predicate -/
open INSERTION_SORT_P2 (sorted empty_sorted singleton_sorted head_sorted
  tail_sorted cons_sorted cons_sorted')

/-
  -----------------------------------------------------------
  MERGE SORT
  -----------------------------------------------------------
-/

@[grind]
theorem split_correct
  (ℓ : List ℕ)
  : let (ℓ₁, ℓ₂) := split ℓ
    (ℓ₁ ++ ℓ₂).Perm ℓ
:= by 
  grind [split, List.take_append_drop] 

@[grind!]
lemma merge_perm
  (ℓ₁ ℓ₂ : List ℕ)
  : (merge ℓ₁ ℓ₂).Perm (ℓ₁ ++ ℓ₂)
:= by
  fun_induction merge ℓ₁ ℓ₂ <;> grind 

@[grind →]
lemma mem_merge {a : ℕ} {m₁ m₂ : List ℕ} : 
    a ∈ merge m₁ m₂ → a ∈ m₁ ∨ a ∈ m₂ 
:= by
  rw [(merge_perm m₁ m₂).mem_iff, List.mem_append]
  exact id

@[grind]
lemma merge_sorted
  {ℓ₁ ℓ₂ : List ℕ}
  : sorted ℓ₁ → sorted ℓ₂ → sorted (merge ℓ₁ ℓ₂)
:= by
  fun_induction merge ℓ₁ ℓ₂ <;> grind [-merge_perm, sorted, List.pairwise_cons, mem_merge] 

lemma merge_sort_perm
  (ℓ : List ℕ)
  : (merge_sort ℓ).Perm ℓ
:= by
  fun_induction merge_sort ℓ <;> grind [split, List.take_append_drop] 

lemma merge_sort_sorted
  (ℓ : List ℕ)
  : sorted (merge_sort ℓ)
:= by
  fun_induction merge_sort ℓ <;> grind [sorted] 
