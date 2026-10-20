/-
  # EXERCISES FOR `L06`

  Fill in the `sorry` for the requested definitions. For each definition the
  `#guard_msgs` below it should pass with no errors.
-/

import Course.CourseLib

topic::P1

variable {α β γ : Type}

/-
  Curry a function, i.e., instead of taking a pair of arguments it takes one
  argument at a time -/
def curry (f : (α × β) → γ) : α → β → γ :=
  fun a b => f (a, b) 

/-- info: true -/
#guard_msgs in
#eval (curry (fun ((a, b) : ℕ × ℕ) => a * b)) 2 3 == 6

/-
  Uncurry a function, i.e., instead of taking one argument at a time it takes a
  pair of arguments -/
def uncurry (f : α → β → γ) : (α × β) → γ :=
  fun (a, b) => f a b 

/-- info: true -/
#guard_msgs in
#eval (uncurry (fun (a b : ℕ) => a * b)) (2, 3) == 6

end_topic P1


topic::P2

/-
  A list of integers -/
inductive MyList
  | nil
  | cons : ℤ → MyList → MyList
deriving BEq

namespace MyList

/- For tests -/
def ℓ₁ : MyList := .cons 1 (.cons 2 (.cons 3 .nil))
def ℓ₂ : MyList := (.cons 1 (.cons 2 .nil))
def ℓ₃ : MyList := (.cons 3 .nil)
def ℓ₄ : MyList := .cons 3 (.cons 2 (.cons 1 .nil))

/-
  The fold function that transforms a `MyList` into an `α`. Takes the list to
  transform, a function that takes the accumulated result so far and an element
  of the list and returns a new result, and the initial value (also the result
  if the list is empty). -/
def fold {α : Type} (ℓ : MyList) (f : α → ℤ → α) (init : α) : α :=
  match ℓ with
  | nil => init 
  | cons h t => fold t f (f init h) 

/-- info: 6 -/
#guard_msgs in
#eval ℓ₁.fold (fun acc z => acc * z) 1

/-
  ## INSTRUCTIONS
  For all definitions below here, use your `fold` definition to define the
  functions rather than direct recursion (you may also use the functions you
  have already defined)
-/

/-
  Returns the reverse of `ℓ` -/
def reverse (ℓ : MyList) : MyList :=
  ℓ.fold (fun acc x => .cons x acc) .nil

/-- info: true -/
#guard_msgs in
#eval ℓ₁.reverse == ℓ₄

/-
  Returns `ℓ₁ ++ ℓ₂` -/
def append (ℓ₁ ℓ₂ : MyList) : MyList :=
  fold (reverse ℓ₁) (fun acc x => .cons x acc) ℓ₂

/-- info: true -/
#guard_msgs in
#eval ℓ₂.append ℓ₃ == ℓ₁

/-
  Returns whether any of the elements satisfy the predicate -/
def any (ℓ : MyList) (P : ℤ → Bool) : Bool :=
  ℓ.fold (fun acc x => acc || P x) False

/-- info: true -/
#guard_msgs in
#eval ℓ₁.any (fun z => z > 2)

/-- info: false -/
#guard_msgs in
#eval ℓ₁.any (fun z => z = 10)

/-
  Returns whether all of the elements satisfy the predicate -/
def all (ℓ : MyList) (P : ℤ → Bool) : Bool :=
  ℓ.fold (fun acc x => acc && P x) True

/-- info: true -/
#guard_msgs in
#eval ℓ₁.all (fun z => z < 10)

/-- info: false -/
#guard_msgs in
#eval ℓ₁.all (fun z => z > 2)

/-
  Returns those elements that satisfy the predicate -/
def filter (ℓ : MyList) (P : ℤ → Bool) : MyList :=
  ℓ.fold (fun acc x => if P x then .cons x acc else acc) .nil

/-- info: true -/
#guard_msgs in
#eval ℓ₁.filter (fun z => z > 2) == ℓ₃

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
  aux [] ℓ
where
  aux (acc : List (String × ℕ)) (ℓ : List String) : List (String × ℕ) :=
    match ℓ with
    | [] => acc
    | x :: xs =>
      let rec update (ℓ' : List (String × ℕ)) : List (String × ℕ) :=
        match ℓ' with
        | [] => [(x, 1)]
        | (key, count) :: ys =>
          if key == x then (key, count + 1) :: ys else (key, count) :: update ys
      aux (update acc) xs 

/-- info: true -/
#guard_msgs in
#eval word_count ["a", "b", "a", "c", "b", "a"] == [("a", 3), ("b", 2), ("c", 1)]

end_topic P3


topic::P4

/-
  A binary tree where every node and leaf has a value -/
inductive Tree
  | leaf : ℕ → Tree
  | node : ℕ → Tree → Tree → Tree
deriving BEq

namespace Tree

/- For tests-/
def t₁ : Tree :=
  .node 1
    (.node 2
      (.leaf 3)
      (.node 4
        (.leaf 5)
        (.leaf 6)))
    (.node 7
      (.node 8
        (.leaf 9)
        (.leaf 10))
      (.node 11
        (.leaf 12)
        (.leaf 13)))

def t₂ : Tree :=
  .node 2
    (.node 4
      (.leaf 6)
      (.node 8
        (.leaf 10)
        (.leaf 12)))
    (.node 14
      (.node 16
        (.leaf 18)
        (.leaf 20))
      (.node 22
        (.leaf 24)
        (.leaf 26)))

def t₃ : Tree :=
  .node 1
    (.node 2
      (.leaf 3)
      (.leaf 4))
    (.leaf 5)

/-
  Returns whether `n` is an element of the tree -/
def mem (t : Tree) (n : ℕ) : Bool :=
  match t with
  | leaf x => n == x
  | node x l r => n == x || mem l n || mem r n

/-- info: true -/
#guard_msgs in
#eval t₁.mem 8

/-- info: false -/
#guard_msgs in
#eval t₁.mem 14

/-
  Outputs a pre-order list of tree elements -/
def toList₁ (t : Tree) : List ℕ :=
  aux [] t
where
  aux (acc : List ℕ) (t : Tree) : List ℕ :=
    match t with
    | leaf x => x :: acc
    | node x l r => x :: aux (aux acc r) l

/-- info: true -/
#guard_msgs in
#eval t₁.toList₁ == [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-
  Outputs a post-order list of tree elements -/
def toList₂ (t : Tree) : List ℕ :=
  aux [] t
where
  aux (acc : List ℕ) (t : Tree) : List ℕ :=
    match t with
    | leaf x => x :: acc
    | node x l r => aux (aux (x :: acc) r) l

/-- info: true -/
#guard_msgs in
#eval t₁.toList₂ == [3, 5, 6, 4, 2, 9, 10, 8, 12, 13, 11, 7, 1]

/-
  Outputs an in-order list of tree elements -/
def toList₃ (t : Tree) : List ℕ :=
  aux [] t
where
  aux (acc : List ℕ) (t : Tree) : List ℕ :=
    match t with
    | leaf x => x :: acc
    | node x l r => aux (x :: aux acc r) l

/-- info: true -/
#guard_msgs in
#eval t₁.toList₃ == [3, 2, 5, 4, 6, 1, 9, 8, 10, 7, 12, 11, 13]

/-
  Maps each tree element to a new element according to `f` -/
def map (t : Tree) (f : ℕ → ℕ) : Tree :=
  match t with
  | leaf x => .leaf (f x)
  | node x l r => .node (f x) (map l f) (map r f)

/-- info: true -/
#guard_msgs in
#eval t₁.map (fun z => 2*z) == t₂

/-
  The fold function on trees. Now `f` takes three arguments: the result of
  folding the left subtree, the result of folding the right subtree, and the
  value at the node. `init` is now a function `leaf` that takes the value at a
  leaf. -/
def fold {α : Type} (t : Tree) (f : α → α → ℕ → α) (leaf : ℕ → α) : α :=
  match t with
  | .leaf x => leaf x
  | node x l r =>
    let accₗ := fold l f leaf
    let accᵣ := fold r f leaf
    f accₗ accᵣ x 

/-- info: 91 -/
#guard_msgs in
#eval t₁.fold (fun accₗ accᵣ n => accₗ + accᵣ + n) id

/-
  Outputs a list of all paths from the root of the tree to a leaf (using the
  value of each node as its identifier). HINT: use the `fold` that you
  implemented above. -/
def paths (t : Tree) : List (List ℕ) :=
  t.fold 
    (fun pathsₗ pathsᵣ x => (pathsₗ ++ pathsᵣ).map (fun path => x :: path)) 
    (fun x => [[x]]) 

/-- info: true -/
#guard_msgs in
#eval t₃.paths == [[1, 2, 3], [1, 2, 4], [1, 5]]

end Tree

end_topic P4
