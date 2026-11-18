/-
  # EXERCISES FOR `L14`

  We revisit `L08` so that we can redo the proofs using `grind` and `aesop`.
  Annotate as you see fit, and see how much of the proofs you can automate.
  Remember that you can annotate things in other files using `attribute`.
-/

import Course.CourseLib
import Course.L08_ExpLang

attribute [grind →] exp_eval_matches_semantics
attribute [aesop safe apply] exp_semantics_matches_eval

@[grind →]
theorem HasType.deterministic
  {Γ : Env} {e : Exp} {τ₁ τ₂ : Ty}
  : HasType Γ e τ₁ → HasType Γ e τ₂ → τ₁ = τ₂
:= by
  intro h₁ h₂
  induction h₁ generalizing τ₂ <;> cases h₂ <;> grind 

@[grind →]
theorem BigstepE.deterministic
  {σ : State} {e : Exp} {v₁ v₂ : Value}
  : BigstepE σ e v₁ → BigstepE σ e v₂ → v₁ = v₂
:= by
  intro h₁ h₂
  induction h₁ generalizing v₂ <;> cases h₂ <;> grind 

inductive Stmt
  | skip    : Stmt
  | assign  : Var → Exp → Stmt
  | seq     : Stmt → Stmt → Stmt
  | ifelse  : Exp → Stmt → Stmt → Stmt
  | whiledo : Exp → Stmt → Stmt

@[aesop unsafe 50% constructors]
inductive BigstepS : State → Stmt → State → Prop
  | skip σ : BigstepS σ .skip σ
  | assign {σ₁ σ₂ x rhs v}:
      BigstepE σ₁ rhs v → v ≠ .error → σ₂ = σ₁.insert x v →
      BigstepS σ₁ (.assign x rhs) σ₂
  | seq {σ₁ σ₂ σ₃ s₁ s₂}:
      BigstepS σ₁ s₁ σ₂ → BigstepS σ₂ s₂ σ₃ →
      BigstepS σ₁ (.seq s₁ s₂) σ₃
  | ifelse_tt {σ₁ σ₂ g tt ff} :
      BigstepE σ₁ g (.bool true) → BigstepS σ₁ tt σ₂ →
      BigstepS σ₁ (.ifelse g tt ff) σ₂
  | ifelse_ff {σ₁ σ₂ g tt ff} :
      BigstepE σ₁ g (.bool false) → BigstepS σ₁ ff σ₂ →
      BigstepS σ₁ (.ifelse g tt ff) σ₂
  | whiledo_tt {σ₁ σ₂ σ₃ g body} :
      BigstepE σ₁ g (.bool true) → BigstepS σ₁ body σ₂ →
      BigstepS σ₂ (.whiledo g body) σ₃ → BigstepS σ₁ (.whiledo g body) σ₃
  | whiledo_ff {σ g body} :
      BigstepE σ g (.bool false) → BigstepS σ (.whiledo g body) σ

@[grind →]
theorem BigstepS.deterministic
  {σ₁ σ₂ σ₃ : State} {s : Stmt}
  : BigstepS σ₁ s σ₂ → BigstepS σ₁ s σ₃ → σ₂ = σ₃
:= by
  intro h₁ h₂
  induction h₁ generalizing σ₃ <;> cases h₂ <;> grind

inductive Result
  | normal (σ : State)
  | error
  | timeout

@[grind]
def clocked_eval (σ : State) (fuel : ℕ) (s : Stmt) : Result :=
  match fuel with
  | 0 => .timeout
  | n + 1 =>
    match s with
    | .skip => .normal σ
    | .assign x rhs =>
      match Exp.eval σ rhs with
      | .error => .error
      | v => .normal (σ.insert x v)
    | .seq s₁ s₂ =>
      match clocked_eval σ n s₁ with
      | .normal σ' => clocked_eval σ' n s₂ 
      | res => res
    | .ifelse guard tt ff =>
      match Exp.eval σ guard with
      | .bool true  => clocked_eval σ n tt 
      | .bool false => clocked_eval σ n ff 
      | _ => .error
    | .whiledo guard body =>
      match Exp.eval σ guard with
      | .bool true  => 
        match clocked_eval σ n body with 
        | .normal σ' => clocked_eval σ' n (.whiledo guard body)
        | res => res
      | .bool false => .normal σ
      | _ => .error

lemma clocked_eval.monotone
  {σ₁ σ₂ : State} {s : Stmt} {n₁ : ℕ} (n₂ : ℕ)
  : clocked_eval σ₁ n₁ s = .normal σ₂ → n₁ ≤ n₂ → clocked_eval σ₁ n₂ s = .normal σ₂
:= by
  fun_induction clocked_eval σ₁ n₁ s generalizing σ₂ n₂ <;> cases n₂ <;> grind

@[aesop unsafe 50% apply]
lemma exists_fuel_one {σ₁ σ₂ : State} {s : Stmt}
    (h : clocked_eval σ₁ 1 s = .normal σ₂) :
    ∃ n, clocked_eval σ₁ n s = .normal σ₂ := ⟨1, h⟩

@[aesop unsafe 50% apply]
lemma exists_fuel_succ {σ₁ σ₂ : State} {s' s : Stmt} {n : ℕ}
    (_ : clocked_eval σ₁ n s' = .normal σ₂)
    (h : clocked_eval σ₁ (n + 1) s = .normal σ₂) :
    ∃ n, clocked_eval σ₁ n s = .normal σ₂ := ⟨n + 1, h⟩

@[aesop unsafe 50% apply]
lemma exists_fuel_add {σ₁ σ₂ σ₃ : State} {s₁ s₂ s : Stmt} {n₁ n₂ : ℕ}
    (_ : clocked_eval σ₁ n₁ s₁ = .normal σ₂)
    (_ : clocked_eval σ₂ n₂ s₂ = .normal σ₃)
    (h : clocked_eval σ₁ (n₁ + n₂ + 1) s = .normal σ₃) :
    ∃ n, clocked_eval σ₁ n s = .normal σ₃ := ⟨n₁ + n₂ + 1, h⟩

theorem stmt_eval_matches_semantics
  {σ₁ σ₂ : State} {s : Stmt}
  : BigstepS σ₁ s σ₂ → ∃ n, clocked_eval σ₁ n s = (.normal σ₂)
:= by
  intro h
  induction h <;> aesop (add safe (by grind [clocked_eval.monotone]))

theorem stmt_semantics_matches_eval
  {σ₁ σ₂ : State} {s : Stmt}
  : (∃ n, clocked_eval σ₁ n s = (.normal σ₂)) → BigstepS σ₁ s σ₂
:= by
  intro ⟨n, h⟩
  fun_induction clocked_eval σ₁ n s generalizing σ₂ <;> aesop (add safe (by grind))
