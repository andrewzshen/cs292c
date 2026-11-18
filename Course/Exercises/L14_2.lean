/-
  # EXERCISES FOR `L14`

  We revisit `L04_2` so that we can redo the proofs using `grind` and `aesop`.
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
  SELECTION SORT
  -----------------------------------------------------------
-/

@[grind, simp]
def select_min (n : ℕ) (ℓ : List ℕ) : ℕ × (List ℕ) :=
  let min := (n :: ℓ).minimum_of_length_pos (by simp)
  (min, (n :: ℓ).erase min)

@[grind ., simp]
lemma select_min_size
  (n : ℕ) (ℓ : List ℕ)
  : let (_, ℓ₁) := select_min n ℓ
    ℓ₁.length = ℓ.length
:= by simp [List.minimum_of_length_pos_mem]

@[grind, simp]
def selection_sort : List ℕ → List ℕ
  | [] => []
  | x :: xs =>
    let mr := select_min x xs
    mr.1 :: (selection_sort mr.2)
termination_by ℓ => ℓ.length
decreasing_by grind

@[grind ., simp]
lemma select_min_perm
  (n : ℕ) (ℓ : List ℕ)
  : let (n₁, ℓ₁) := select_min n ℓ
    (n₁ :: ℓ₁).Perm (n :: ℓ)
:= by
  grind [select_min, List.minimum_of_length_pos_mem, List.count_pos_iff]

@[grind ., simp]
lemma select_min_smallest
  (n : ℕ) (ℓ : List ℕ)
  : let (n₁, _) := select_min n ℓ
    (∀ m ∈ (n :: ℓ), n₁ ≤ m)
:= by
  grind [select_min, List.minimum_of_length_pos_le_of_mem]

@[grind →]
lemma select_min_perm_of_perm {n : ℕ} {ℓ l : List ℕ}
    (h : l.Perm (select_min n ℓ).2) :
    ((select_min n ℓ).1 :: l).Perm (n :: ℓ) :=
  (h.cons _).trans (select_min_perm n ℓ)

@[grind →]
lemma select_min_le {n m : ℕ} {ℓ : List ℕ}
    (hm : m ∈ n :: ℓ) : (select_min n ℓ).1 ≤ m :=
  select_min_smallest n ℓ m hm

@[grind →]
lemma mem_select_min_snd {n m : ℕ} {ℓ : List ℕ}
    (hm : m ∈ (select_min n ℓ).2) : m ∈ n :: ℓ := by
  simp only [select_min] at hm
  exact List.mem_of_mem_erase hm

lemma selection_sort_perm
  (ℓ : List ℕ)
  : (selection_sort ℓ).Perm ℓ
:= by
  fun_induction selection_sort ℓ <;> grind
  
@[grind =]
lemma mem_selection_sort {m : ℕ} {ℓ : List ℕ} :
    m ∈ selection_sort ℓ ↔ m ∈ ℓ :=
  (selection_sort_perm ℓ).mem_iff

lemma selection_sort_sorted
  (ℓ : List ℕ)
  : sorted (selection_sort ℓ)
:= by
  fun_induction selection_sort ℓ <;> grind [sorted, List.pairwise_cons]
