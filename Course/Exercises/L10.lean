/-
  # EXERCISES FOR `L10`

  The three topics below each implement vectors (lists of a given length) in a
  different way, all based on dependent types. Fill in the `sorry` for each
  definition in each topic. The `#guard_msgs` should all pass without errors.
-/

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
  | cons {n} : α → Vec α n → Vec α (n + 1)

namespace Vec

variable {α β : Type}

def head {n : ℕ} (v : Vec α (n + 1)) : α :=
  match v with
  | .cons x _ => x 

def tail {n : ℕ} (v : Vec α (n + 1)) : Vec α n :=
  match v with
  | .cons _ xs => xs

def get {n : ℕ} (v : Vec α (n + 1)) (i : Fin (n + 1)) : α :=
  aux v i
where
  aux {m : ℕ} : Vec α m → Fin m → α
    | .cons x _, ⟨0, _⟩ => x 
    | .cons _ xs, ⟨i + 1, h⟩ => aux xs ⟨i, Nat.lt_of_succ_lt_succ h⟩

def zip {n : ℕ} (v₁ : Vec α n) (v₂ : Vec β n) : Vec (α × β) n :=
  match v₁, v₂ with
  | .nil, .nil => .nil 
  | .cons x xs, .cons y ys => .cons (x, y) (zip xs ys)

def append {n m : ℕ} (v₁ : Vec α n) (v₂ : Vec α m) : Vec α (n + m) :=
  match v₁ with
  | .nil => 
    (Nat.zero_add m).symm ▸ v₂
  | @Vec.cons _ k x xs =>
    (Nat.succ_add k m) ▸ .cons x (append xs v₂) 

def replicate (a : α) (num : ℕ) : Vec α num :=
  match num with
  | 0 => .nil
  | n + 1 => .cons a (replicate a n)

def filter {n: ℕ} (v : Vec α n) (P : α → Bool) : Σ k, Vec α k :=
  match v with
  | .nil => ⟨0, .nil⟩ 
  | .cons x xs =>
    let ⟨k, res⟩ := filter xs P 
    if P x then
      ⟨k + 1, .cons x res⟩
    else
      ⟨k, res⟩

/- --- TESTS --- -/

def v₁ : Vec ℕ 3 := .cons 1 (.cons 2 (cons 3 .nil))
def v₂ : Vec ℕ 2 := .cons 4 (.cons 5 .nil)
def v₃ : Vec Bool 3 := .cons true (.cons false (cons true .nil))

/-- info: 3 -/
#guard_msgs in
#eval v₁.tail.tail.head

/-- info: 2 -/
#guard_msgs in
#eval v₁.get (1 : Fin 3)

/-- info: (1, true) -/
#guard_msgs in
#eval (v₁.zip v₃).head

/-- info: 4 -/
#guard_msgs in
#eval (v₁.append v₂).get (3 : Fin 5)

/-- info: "a" -/
#guard_msgs in
#eval (replicate "a" 3).get (2 : Fin 3)

/-- info: 2 -/
#guard_msgs in
#eval (v₁.filter (· ≤ 2)).1

end Vec
end_topic V1


topic::V2

structure Vec (α : Type) (n : ℕ) where
  ℓ : List α
  len : ℓ.length = n

namespace Vec

variable {α β : Type} {n m : ℕ}

def head (v : Vec α (n + 1)) : α :=
  match h : v.ℓ with
  | [] => by
    have h_len : v.ℓ.length = n + 1 := v.len
    rw [h] at h_len 
    contradiction
  | x :: _ => x 

def tail (v : Vec α (n + 1)) : Vec α n :=
  ⟨v.ℓ.tail, by simp [v.len]⟩

def get (v : Vec α n) (i : Fin n) : α :=
  v.ℓ[i.val]'(by rw [v.len]; exact i.isLt) 

def zip (v₁ : Vec α n) (v₂ : Vec β n) : Vec (α × β) n :=
  ⟨v₁.ℓ.zip v₂.ℓ, by simp [v₁.len, v₂.len]⟩

def append (v₁ : Vec α n) (v₂ : Vec α m) : Vec α (n+m) :=
  ⟨v₁.ℓ ++ v₂.ℓ, by simp [v₁.len, v₂.len]⟩

def replicate (a : α) (num : ℕ) : Vec α num :=
  ⟨List.replicate num a, List.length_replicate⟩ 

def filter (v : Vec α n) (P : α → Bool) : Σ k, Vec α k :=
  let ℓ' := v.ℓ.filter P
  ⟨ℓ'.length, ⟨ℓ', rfl⟩⟩ 

/- --- TESTS --- -/

def v₁ : Vec ℕ 3 := Vec.mk [1, 2, 3] (by simp)
def v₂ : Vec ℕ 2 := Vec.mk [4, 5] (by simp)
def v₃ : Vec Bool 3 := Vec.mk [true, false, true] (by simp)

/-- info: 3 -/
#guard_msgs in
#eval v₁.tail.tail.head

/-- info: 2 -/
#guard_msgs in
#eval v₁.get (1 : Fin 3)

/-- info: (1, true) -/
#guard_msgs in
#eval (v₁.zip v₃).head

/-- info: 4 -/
#guard_msgs in
#eval (v₁.append v₂).get (3 : Fin 5)

/-- info: "a" -/
#guard_msgs in
#eval (replicate "a" 3).get (2 : Fin 3)

/-- info: 2 -/
#guard_msgs in
#eval (v₁.filter (· ≤ 2)).1

end Vec
end_topic V2


topic::V3

def Vec (α : Type) (n : ℕ) := Fin n → α

namespace Vec

variable {α β : Type} {n m : ℕ}

def head (v : Vec α (n + 1)) : α :=
  v ⟨0, Nat.succ_pos n⟩ 

def tail (v : Vec α (n + 1)) : Vec α n :=
  fun i => v ⟨i.val + 1, Nat.add_lt_add_right i.isLt 1⟩

def get (v : Vec α n) (i : Fin n) : α :=
  v i 

def zip (v₁ : Vec α n) (v₂ : Vec β n) : Vec (α × β) n :=
  fun i => (v₁ i, v₂ i) 

def append (v₁ : Vec α n) (v₂ : Vec α m) : Vec α (n + m) :=
  fun i =>
    if h : i.val < n then
      v₁ ⟨i.val, h⟩
    else 
      v₂ ⟨i.val - n, by lia⟩

def replicate (a : α) (num : ℕ) : Vec α num :=
  fun _ => a 

def filter (v : Vec α n) (P : α → Bool) : Σ k, Vec α k :=
  let ℓ := v 
    |> List.ofFn 
    |>.filter P
  ⟨ℓ.length, fun i => ℓ[i.val]'(i.isLt)⟩

/- --- TESTS --- -/

def v₁ : Vec ℕ 3 := fun n =>
  if n = 0 then 1
  else if n = 1 then 2
  else 3

def v₂ : Vec ℕ 2 := fun n =>
  if n = 0 then 4
  else 5

def v₃ : Vec Bool 3 := fun n =>
  if n = 0 || n = 2 then true
  else false

/-- info: 3 -/
#guard_msgs in
#eval v₁.tail.tail.head

/-- info: 2 -/
#guard_msgs in
#eval v₁.get (1 : Fin 3)

/-- info: (1, true) -/
#guard_msgs in
#eval (v₁.zip v₃).head

/-- info: 4 -/
#guard_msgs in
#eval (v₁.append v₂).get (3 : Fin 5)

/-- info: "a" -/
#guard_msgs in
#eval (replicate "a" 3).get (2 : Fin 3)

/-- info: 2 -/
#guard_msgs in
#eval (v₁.filter (· ≤ 2)).1

end Vec
end_topic V3
