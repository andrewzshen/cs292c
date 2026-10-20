/-
  # EXERCISES FOR `L04`

  Mergesort and selection sort.

  ## INSTRUCTIONS

  Fill in the `sorry` for the theorems below.
-/

import Course.CourseLib
import Course.L03_Sorting
import Course.L04_SortingDeux

/-
  HINT: don't forget about the `sorted` lemmas we proved in the lecure notes;
  you will need them in the following exercises -/

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

/-
  HINT: recall the following theorems, used in `L03_Sorting` -/
#check if_pos
#check if_neg
#check List.Perm.nil
#check List.Perm.refl
#check List.Perm.trans
#check List.Perm.cons
#check List.Perm.swap
#check List.Perm.mem_iff
#check List.mem_cons
#check List.pairwise_cons

/-
  HINT: you may also find the following theorems helpful -/
#check List.Perm.append
#check List.perm_comm
#check List.perm_middle

theorem split_correct
  (ℓ : List ℕ)
  : let (ℓ₁, ℓ₂) := split ℓ
    (ℓ₁ ++ ℓ₂).Perm ℓ
:= by
  simp [split] 

lemma merge_perm
  (ℓ₁ ℓ₂ : List ℕ)
  : (merge ℓ₁ ℓ₂).Perm (ℓ₁ ++ ℓ₂)
:= by
  induction ℓ₁ generalizing ℓ₂ with
  | nil => simp [merge]
  | cons x ℓ₁ ih₁ =>
    induction ℓ₂ with
    | nil => simp [merge]
    | cons y ℓ₂ ih₂ =>
      by_cases h : x ≤ y
      · simp only [merge, if_pos h]
        exact List.Perm.cons x (ih₁ (y :: ℓ₂))
      · simp only [merge, if_neg h]
        exact (List.Perm.cons y ih₂).trans List.perm_middle.symm

lemma merge_sorted
  {ℓ₁ ℓ₂ : List ℕ}
  : sorted ℓ₁ → sorted ℓ₂ → sorted (merge ℓ₁ ℓ₂)
:= by
  have mem_merge : ∀ (a : ℕ) (m₁ m₂ : List ℕ), a ∈ merge m₁ m₂ → a ∈ m₁ ∨ a ∈ m₂ :=
    fun a m₁ m₂ h => List.mem_append.mp ((merge_perm m₁ m₂).mem_iff.mp h)
  fun_induction merge ℓ₁ ℓ₂ with
  | case1 _ => 
    intro _ h
    exact h
  | case2 _ _ => 
    intro h _ 
    exact h
  | case3 x ℓ₁ y ℓ₂ hxy ih =>
    intro h₁ h₂
    obtain ⟨hx, h₁'⟩ := List.pairwise_cons.mp h₁
    refine List.pairwise_cons.mpr ⟨?_, ih h₁' h₂⟩ 
    intro b hb
    cases mem_merge b _ _ hb with
    | inl hb₁ => exact hx b hb₁
    | inr hb₂ =>
      cases List.mem_cons.mp hb₂ with
      | inl heq =>
        subst heq
        exact hxy
      | inr hb₂' =>
        exact le_trans hxy ((List.pairwise_cons.mp h₂).1 b hb₂')
  | case4 x ℓ₁ y ℓ₂ hxy ih =>
    intro h₁ h₂
    obtain ⟨hy, h₂'⟩ := List.pairwise_cons.mp h₂
    refine List.pairwise_cons.mpr ⟨?_, ih h₁ h₂'⟩ 
    intro b hb
    have hyx : y ≤ x := Nat.le_of_not_le hxy
    cases mem_merge b _ _ hb with
    | inl hb₁ => 
      cases List.mem_cons.mp hb₁ with
      | inl heq =>
        subst heq
        exact hyx
      | inr hb₁' =>
        exact le_trans hyx ((List.pairwise_cons.mp h₁).1 b hb₁')
    | inr hb₂ =>
      exact hy b hb₂

lemma merge_sort_perm
  (ℓ : List ℕ)
  : (merge_sort ℓ).Perm ℓ
:= by
  fun_induction merge_sort ℓ with
  | case1 => rfl
  | case2 _ => rfl 
  | case3 x y ℓ ℓs ih₁ ih₂ =>
    have h1 : (merge (merge_sort (split (x :: y :: ℓ)).1) (merge_sort (split (x :: y :: ℓ)).2)).Perm
                  (merge_sort (split (x :: y :: ℓ)).1 ++ merge_sort (split (x :: y :: ℓ)).2) :=
    merge_perm _ _
    have h2 : (merge_sort (split (x :: y :: ℓ)).1 ++ merge_sort (split (x :: y :: ℓ)).2).Perm
                ((split (x :: y :: ℓ)).1 ++ (split (x :: y :: ℓ)).2) :=
      ih₁.append ih₂
    have h3 : ((split (x :: y :: ℓ)).1 ++ (split (x :: y :: ℓ)).2).Perm (x :: y :: ℓ) :=
      split_correct (x :: y :: ℓ)
    exact h1.trans (h2.trans h3)

lemma merge_sort_sorted
  (ℓ : List ℕ)
  : sorted (merge_sort ℓ)
:= by
  fun_induction merge_sort ℓ with
  | case1 => simp [sorted] 
  | case2 _ => simp [sorted] 
  | case3 x y ℓ ℓs ih₁ ih₂ => exact merge_sorted ih₁ ih₂
