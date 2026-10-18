/-
  # EXERCISES FOR `L10`

  The three topics below each implement vectors (lists of a given length) in a
  different way, all based on dependent types. Fill in the `sorry` for each
  definition in each topic. The `#guard_msgs` in `L10_tests.lean` should all
  pass without errors. -/

import Course.CourseLib

topic::V1
/-
  HINT:

  - This is the most complicated of the three approaches; it will require you to manipulate the types and use proofs to convince Lean that everything type checks

  - For _some_ of the pattern-matches on `Vec` you'll want to simultaneously pattern-match on `n` (the size of the `Vec`) in order to have the necessary information in each branch

  - Remember that you can propagate givens about the results of conditional guards or pattern-matches by using `h :` in the guard or expression being matched, as described in `L05_ComprehensiveRecap` when talking about well-founded recursion

  - For some of the functions the type of your result may be equivalent, but not identical, to the type that Lean is expecting (e.g., `n + 0` instead of `n`). You can enter tactic mode and use `rw` to modify the expected type, then `exact` to give the actual result. In `L12_DExpLang` we'll see a more convenient way to do the same thing that doesn't require tactics.
-/

inductive Vec (α : Type) : ℕ → Type
  | nil : Vec α 0
  | cons {n} : α → Vec α n → Vec α (n+1)

namespace Vec

variable {α β : Type}

def head {n: ℕ} (v : Vec α (n+1)) : α :=
  sorry

def tail {n: ℕ} (v : Vec α (n+1)) : Vec α n :=
  sorry

def get {n: ℕ} (v : Vec α (n+1)) (i : Fin (n+1)) : α :=
  sorry

def zip {n : ℕ} (v₁ : Vec α n) (v₂ : Vec β n) : Vec (α × β) n :=
  sorry

def append {n m : ℕ} (v₁ : Vec α n) (v₂ : Vec α m) : Vec α (n+m) :=
  sorry

def replicate (a : α) (num : ℕ) : Vec α num :=
  sorry

def filter {n: ℕ} (v : Vec α n) (P : α → Bool) : Σ k, Vec α k :=
  sorry

end Vec
end_topic V1


topic::V2

structure Vec (α : Type) (n : ℕ) where
  ℓ : List α
  len : ℓ.length = n

namespace Vec

variable {α β : Type} {n m : ℕ}

def head (v : Vec α (n+1)) : α :=
  sorry

def tail (v : Vec α (n+1)) : Vec α n :=
  sorry

def get (v : Vec α n) (i : Fin n) : α :=
  sorry

def zip (v₁ : Vec α n) (v₂ : Vec β n) : Vec (α × β) n :=
  sorry

def append (v₁ : Vec α n) (v₂ : Vec α m) : Vec α (n+m) :=
  sorry

def replicate (a : α) (num : ℕ) : Vec α num :=
  sorry

def filter (v : Vec α n) (P : α → Bool) : Σ k, Vec α k :=
  sorry

end Vec
end_topic V2


topic::V3

def Vec (α : Type) (n : ℕ) := Fin n → α

namespace Vec

variable {α β : Type} {n m : ℕ}

def head (v : Vec α (n+1)) : α :=
  sorry

def tail (v : Vec α (n+1)) : Vec α n :=
  sorry

def get (v : Vec α n) (i : Fin n) : α :=
  sorry

def zip (v₁ : Vec α n) (v₂ : Vec β n) : Vec (α × β) n :=
  sorry

def append (v₁ : Vec α n) (v₂ : Vec α m) : Vec α (n+m) :=
  sorry

def replicate (a : α) (num : ℕ) : Vec α num :=
  sorry

def filter (v : Vec α n) (P : α → Bool) : Σ k, Vec α k :=
  sorry

end Vec
end_topic V3
