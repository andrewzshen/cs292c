/-
  # EXERCISES FOR `L06`

  Fill in the `sorry` for the requested definitions. For each definition the
  `#guard_msgs` in `L06_tests.lean` should pass with no errors.
-/

import Course.CourseLib

topic::P1

variable {α β γ : Type}

/-
  Curry a function, i.e., instead of taking a pair of arguments it takes one
  argument at a time -/
def curry (f : (α × β) → γ) : α → β → γ :=
  sorry

/-
  Uncurry a function, i.e., instead of taking one argument at a time it takes a
  pair of arguments -/
def uncurry (f : α → β → γ) : (α × β) → γ :=
  sorry

end_topic P1


topic::P2

/-
  A list of integers -/
inductive MyList
  | nil
  | cons : ℤ → MyList → MyList
deriving BEq

namespace MyList

/-
  The fold function that transforms a `MyList` into an `α`. Takes the list to
  transform, a function that takes the accumulated result so far and an element
  of the list and returns a new result, and the initial value (also the result
  if the list is empty). -/
def fold {α : Type} (ℓ : MyList) (f : α → ℤ → α) (init : α) : α :=
  sorry

/-
  ## INSTRUCTIONS
  For all definitions below here, use your `fold` definition to define the
  functions rather than direct recursion (you may also use the functions you
  have already defined)
-/

/-
  Returns the reverse of `ℓ` -/
def reverse (ℓ : MyList) : MyList :=
  sorry

/-
  Returns `ℓ₁ ++ ℓ₂` -/
def append (ℓ₁ ℓ₂ : MyList) : MyList :=
  sorry

/-
  Returns whether any of the elements satisfy the predicate -/
def any (ℓ : MyList) (P : ℤ → Bool) : Bool :=
  sorry

/-
  Returns whether all of the elements satisfy the predicate -/
def all (ℓ : MyList) (P : ℤ → Bool) : Bool :=
  sorry

/-
  Returns those elements that satisfy the predicate -/
def filter (ℓ : MyList) (P : ℤ → Bool) : MyList :=
  sorry

end MyList

end_topic P2


topic::P3

/-
  Fill in the function so that it outputs a list of pairs `(str, n)` s.t. `n` is
  the number of times `str` appears in the input list, in the order that `str`
  first appears in the input list. The `#guard_msgs` test immediately below
  should pass with no errors. You may define nested helper functions if you find
  them helpful. -/
def word_count (ℓ : List String) : List (String × ℕ) :=
  sorry

end_topic P3


topic::P4

/-
  A binary tree where every node and leaf has a value -/
inductive Tree
  | leaf : ℕ → Tree
  | node : ℕ → Tree → Tree → Tree
deriving BEq

namespace Tree

/-
  Returns whether `n` is an element of the tree -/
def mem (t : Tree) (n : ℕ) : Bool :=
  sorry

/-
  Outputs a pre-order list of tree elements -/
def toList₁ (t : Tree) : List ℕ :=
  sorry

/-
  Outputs a post-order list of tree elements -/
def toList₂ (t : Tree) : List ℕ :=
  sorry

/-
  Outputs an in-order list of tree elements -/
def toList₃ (t : Tree) : List ℕ :=
  sorry

/-
  Maps each tree element to a new element according to `f` -/
def map (t : Tree) (f : ℕ → ℕ) : Tree :=
  sorry

/-
  The fold function on trees. Now `f` takes three arguments: the result of
  folding the left subtree, the result of folding the right subtree, and the
  value at the node. `init` is now a function `leaf` that takes the value at a
  leaf. -/
def fold {α : Type} (t : Tree) (f : α → α → ℕ → α) (leaf : ℕ → α) : α :=
  sorry

/-
  Outputs a list of all paths from the root of the tree to a leaf (using the
  value of each node as its identifier). HINT: use the `fold` that you
  implemented above. -/
def paths (t : Tree) : List (List ℕ) :=
  sorry

end Tree

end_topic P4
