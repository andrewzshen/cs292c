import Course.Exercises.L06

namespace P1

/-- info: true -/
#guard_msgs in
#eval (curry (fun ((a, b) : ℕ × ℕ) => a * b)) 2 3 == 6

/-- info: true -/
#guard_msgs in
#eval (uncurry (fun (a b : ℕ) => a * b)) (2, 3) == 6

end P1

namespace P2

def ℓ₁ : MyList := .cons 1 (.cons 2 (.cons 3 .nil))
def ℓ₂ : MyList := (.cons 1 (.cons 2 .nil))
def ℓ₃ : MyList := (.cons 3 .nil)
def ℓ₄ : MyList := .cons 3 (.cons 2 (.cons 1 .nil))

/-- info: true -/
#guard_msgs in
#eval ℓ₁.fold (fun acc z => acc * z) 1 == 6

/-- info: true -/
#guard_msgs in
#eval ℓ₁.reverse == ℓ₄

/-- info: true -/
#guard_msgs in
#eval ℓ₂.append ℓ₃ == ℓ₁

/-- info: true -/
#guard_msgs in
#eval ℓ₁.any (fun z => z > 2)

/-- info: true -/
#guard_msgs in
#eval !ℓ₁.any (fun z => z = 10)

/-- info: true -/
#guard_msgs in
#eval ℓ₁.all (fun z => z < 10)

/-- info: true -/
#guard_msgs in
#eval !ℓ₁.all (fun z => z > 2)

/-- info: true -/
#guard_msgs in
#eval ℓ₁.filter (fun z => z > 2) == ℓ₃

end P2

namespace P3

/-- info: true -/
#guard_msgs in
#eval word_count ["a", "b", "a", "c", "b", "a"] == [("a", 3), ("b", 2), ("c", 1)]

end P3

namespace P4

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

/-- info: true -/
#guard_msgs in
#eval t₁.mem 8

/-- info: true -/
#guard_msgs in
#eval !t₁.mem 14

/-- info: true -/
#guard_msgs in
#eval t₁.toList₁ == [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- info: true -/
#guard_msgs in
#eval t₁.toList₂ == [3, 5, 6, 4, 2, 9, 10, 8, 12, 13, 11, 7, 1]

/-- info: true -/
#guard_msgs in
#eval t₁.toList₃ == [3, 2, 5, 4, 6, 1, 9, 8, 10, 7, 12, 11, 13]

/-- info: true -/
#guard_msgs in
#eval t₁.map (fun z => 2*z) == t₂

/-- info: true -/
#guard_msgs in
#eval t₁.fold (fun accₗ accᵣ n => accₗ + accᵣ + n) id == 91

/-- info: true -/
#guard_msgs in
#eval t₃.paths == [[1, 2, 3], [1, 2, 4], [1, 5]]

end P4
