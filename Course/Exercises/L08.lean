/-
  # EXERCISES FOR `L08`

  Fill in the `sorry` in the theorems and definitions below. Feel free to create
  additional lemmas as you find them helpful.
-/

import Course.CourseLib
import Course.L08_ExpLang

/-
  Determinism is a generally useful property to have; we can prove that both
  `HasType` and `BigstepE` are deterministic -/

/-
  HINT: for each of the following two proofs, many cases are redundant and can
  be collapsed together if you architect the proof the right way -/

theorem HasType.deterministic
  {Γ : Env} {e : Exp} {τ₁ τ₂ : Ty}
  : HasType Γ e τ₁ → HasType Γ e τ₂ → τ₁ = τ₂
:= by
  intro h₁ h₂
  match h₁, h₂ with
  | .int, .int | .bool, .bool 
  | .neg _, .neg _ | .not _, .not _ => rfl

  | .var h₁_lookup, .var h₂_lookup =>
    rw [h₁_lookup] at h₂_lookup
    injection h₂_lookup

  | .add_mul _ _ _, .add_mul _ _ _
  | .le _ _, .le _ _ 
  | .and_or _ _ _, .and_or _ _ _ => rfl 

  | .add_mul h_op _ _, .le _ _ 
  | .le _ _, .add_mul h_op _ _ => cases h_op <;> contradiction

  | .add_mul h₁_op _ _, .and_or h₂_op _ _
  | .and_or h₁_op _ _, .add_mul h₂_op _ _ =>
    cases h₁_op with
    | inl h_add =>
      cases h_add
      cases h₂_op with
      | inl h_and => cases h_and
      | inr h_or => cases h_or
    | inr h_mul =>
      cases h_mul
      cases h₂_op with
      | inl h_and => cases h_and
      | inr h_or => cases h_or
      
  | .le _ _, .and_or _ _ _
  | .and_or _ _ _, .le _ _ => rfl 

/-
  HINT: Remember about `generalizing` if the induction hypothesis needs to be
  strengthened -/
theorem BigstepE.deterministic
  {σ : State} {e : Exp} {v₁ v₂ : Value}
  : BigstepE σ e v₁ → BigstepE σ e v₂ → v₁ = v₂
:= by
  intro h₁ h₂ 
  match h₁, h₂ with
  | .int _, .int _ | .bool _, .bool _ => rfl

  | .var h₁_lookup, .var h₂_lookup => 
    rw [h₁_lookup] at h₂_lookup
    injection h₂_lookup

  | .add h₁_left h₁_right, .add h₂_left h₂_right 
  | .mul h₁_left h₁_right, .mul h₂_left h₂_right 
  | .le h₁_left h₁_right, .le h₂_left h₂_right 
  | .and h₁_left h₁_right, .and h₂_left h₂_right 
  | .or h₁_left h₁_right, .or h₂_left h₂_right =>
    have h_left := BigstepE.deterministic h₁_left h₂_left
    have h_right := BigstepE.deterministic h₁_right h₂_right
    match h_left, h_right with
    | rfl, rfl => rfl

  | .neg h₁_sub, .neg h₂_sub | .not h₁_sub, .not h₂_sub =>
    have h_sub := BigstepE.deterministic h₁_sub h₂_sub
    match h_sub with
    | rfl => rfl

/-
  We extend `ExpLang` to include statements, turning it into a simple imperative
  programming language. `skip` does nothing; `assign` update a variable's value;
  `seq` sequences two statements; `ifelse` is a conditional branch; `whiledo` is
  a while loop. -/
inductive Stmt
  | skip    : Stmt
  | assign  : Var → Exp → Stmt
  | seq     : Stmt → Stmt → Stmt
  | ifelse  : Exp → Stmt → Stmt → Stmt
  | whiledo : Exp → Stmt → Stmt

/-
  The semantics of evaluating statements. `BigstepS σ₁ s σ₂` means that under
  state `σ₁` evaluating statement `s` results in state `σ₂`. Notice that because
  we're defining an inductive predicate there is no issue with the fact that a
  while loop may never terminate: if `s` is nonterminating when starting from
  `σ₁`, then there just doesn't exist any `σ₂` s.t. `BigstepS σ₁ s σ₂`. Again
  importantly, note that type-incorrect statements (e.g., when the conditional
  guard doesn't evaluate to a boolean) do not have any defined transitions. -/
inductive BigstepS : State → Stmt → State → Prop
  | skip σ : BigstepS σ .skip σ
  | assign {σ₁ σ₂ x rhs v} :
      BigstepE σ₁ rhs v → v ≠ .error → σ₂ = σ₁.insert x v →
      BigstepS σ₁ (.assign x rhs) σ₂
  | seq {σ₁ σ₂ σ₃ s₁ s₂} :
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

/-
  HINT: you can annotate the constructors of `BigstepS` for `simp` as shown for
  `HasType` and `BigstepE` in `L08_ExpLang` -/

/-
  HINT: Remember about `generalizing` if the induction hypothesis needs to be
  strengthened -/
theorem BigstepS.deterministic
  {σ₁ σ₂ σ₃ : State} {s : Stmt}
  : BigstepS σ₁ s σ₂ → BigstepS σ₁ s σ₃ → σ₂ = σ₃
:= by
  intro h₁ h₂ 
  match h₁, h₂ with
  | .skip _, .skip _ => rfl  
  
  | .assign h₁_e _ h₁_eq, .assign h₂_e _ h₂_eq =>
    have h_v := BigstepE.deterministic h₁_e h₂_e
    subst h_v h₁_eq h₂_eq
    rfl
    
  | .seq h₁_a h₁_b, .seq h₂_a h₂_b =>
    have h_mid := BigstepS.deterministic h₁_a h₂_a
    subst h_mid
    exact BigstepS.deterministic h₁_b h₂_b

  | .ifelse_tt _ h₁_body, .ifelse_tt _ h₂_body 
  | .ifelse_ff _ h₁_body, .ifelse_ff _ h₂_body => 
    exact BigstepS.deterministic h₁_body h₂_body  

  | .ifelse_tt h₁_guard _, .ifelse_ff h₂_guard _
  | .ifelse_ff h₁_guard _, .ifelse_tt h₂_guard _ =>
    have h_eq := BigstepE.deterministic h₁_guard h₂_guard
    injection h_eq

  | .whiledo_tt _ _ _, .whiledo_tt _ _ _ => sorry 
  | .whiledo_tt _ _ _, .whiledo_ff _ => sorry 
  | .whiledo_ff _, .whiledo_tt _ _ _ => sorry
  | .whiledo_ff _, .whiledo_ff _ => sorry

/-
  We will write an interpreter for statements. Because while loops may not
  terminate we will have to use clocked recursion. We'll want to distinguish
  between executions that fail due to running out the clock vs those that fail
  due to actual errors. -/
inductive Result
  | normal (σ : State)
  | error
  | timeout

/-
  Fill in the implementation to match the semantics described above. If the fuel
  runs out return `Result.timeout`; if there is no valid result according to the
  semantics then return `Result.error`. Use the existing `Exp.eval` for
  evaluating expressions. -/
@[simp]
def clocked_eval (σ : State) (fuel : ℕ) (s : Stmt) : Result :=
  sorry

/-
  This lemma will be useful for proving the interpreter is correct. Remember
  about `generalizing` if the induction hypothesis needs to be strengthened. -/
lemma clocked_eval.monotone
  {σ₁ σ₂ : State} {s : Stmt} {fuel₁ : ℕ} (fuel₂ : ℕ)
  : clocked_eval σ₁ fuel₁ s = .normal σ₂ →
      fuel₁ ≤ fuel₂ → clocked_eval σ₁ fuel₂ s = .normal σ₂
:= by
  sorry

/-
  HINT: Remember that we have already proven `exp_eval_matches_semantics` and
  you can use that theorem in this proof, along with `clocked_eval.monotone`
  that we proved above. When using `clocked_eval.monotone` and `exists`, watch
  out for "off by one" errors that make the proof impossible. -/
theorem stmt_eval_matches_semantics
  {σ₁ σ₂ : State} {s : Stmt}
  : BigstepS σ₁ s σ₂ → ∃ n, clocked_eval σ₁ n s = (.normal σ₂)
:= by
  sorry

/-
  HINT: Remember that we have already proven `exp_semantics_matches_eval` and
  you can use that theorem in this proof. Remember about `generalizing` if the
  induction hypothesis needs to be strengthened. -/
theorem stmt_semantics_matches_eval
  {σ₁ σ₂ : State} {s : Stmt}
  : (∃ n, clocked_eval σ₁ n s = (.normal σ₂)) → BigstepS σ₁ s σ₂
:= by
  sorry
