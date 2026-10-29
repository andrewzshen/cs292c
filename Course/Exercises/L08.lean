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
  | .le _ _, .add_mul h_op _ _ => 
    cases h_op <;> contradiction

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

  | .add h₁_lhs h₁_rhs, .add h₂_lhs h₂_rhs
  | .mul h₁_lhs h₁_rhs, .mul h₂_lhs h₂_rhs 
  | .le  h₁_lhs h₁_rhs, .le  h₂_lhs h₂_rhs 
  | .and h₁_lhs h₁_rhs, .and h₂_lhs h₂_rhs 
  | .or  h₁_lhs h₁_rhs, .or  h₂_lhs h₂_rhs =>
    have h_lhs := BigstepE.deterministic h₁_lhs h₂_lhs
    have h_rhs := BigstepE.deterministic h₁_rhs h₂_rhs
    match h_lhs, h_rhs with
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
    contradiction

  | .whiledo_tt _ h₁_body h₁_r, .whiledo_tt _ h₂_body h₂_r =>
    have h_mid := BigstepS.deterministic h₁_body h₂_body
    subst h_mid
    exact BigstepS.deterministic h₁_r h₂_r
    
  | .whiledo_tt h₁_guard _ _, .whiledo_ff h₂_guard
  | .whiledo_ff h₁_guard, .whiledo_tt h₂_guard _ _ => 
    have h_eq := BigstepE.deterministic h₁_guard h₂_guard
    injection h_eq 
    contradiction

  | .whiledo_ff _, .whiledo_ff _ => rfl 

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

/-
  This lemma will be useful for proving the interpreter is correct. Remember
  about `generalizing` if the induction hypothesis needs to be strengthened. -/
lemma clocked_eval.monotone
  {σ₁ σ₂ : State} {s : Stmt} {fuel₁ : ℕ} (fuel₂ : ℕ)
  : clocked_eval σ₁ fuel₁ s = .normal σ₂ →
    fuel₁ ≤ fuel₂ → clocked_eval σ₁ fuel₂ s = .normal σ₂
:= by
  intro h_eval h_le
  induction fuel₁ generalizing σ₁ σ₂ s fuel₂ with
  | zero =>
    simp [clocked_eval] at h_eval
  | succ n ih =>
    cases fuel₂ with
    | zero => 
      simp_all [clocked_eval] 
    | succ m =>
      cases s with
      | skip | assign _ _ =>
        simp_all [clocked_eval]
      | seq s₁ s₂ =>
        simp_all [clocked_eval]
        cases h_s₁ : clocked_eval σ₁ n s₁ with
        | normal σ' => 
          rw [h_s₁] at h_eval
          have ih₁ := ih m h_s₁ h_le
          have ih₂ := ih m h_eval h_le
          simp [ih₁, ih₂]
        | _ =>
          rw [h_s₁] at h_eval
          contradiction
      | ifelse guard tt ff =>
        simp_all [clocked_eval] 
        split at h_eval <;> try contradiction
        · have ih_tt := ih m h_eval h_le
          exact ih_tt
        · have ih_ff := ih m h_eval h_le
          exact ih_ff
      | whiledo guard body =>
        simp [clocked_eval] at h_eval ⊢
        cases h_g : Exp.eval σ₁ guard with
        | bool b =>
          cases b with
          | true =>
            simp_all
            cases h_body : clocked_eval σ₁ n body with
            | normal σ' =>
              rw [h_body] at h_eval
              have ih_body := ih m h_body h_le
              have ih_loop := ih m h_eval h_le
              simp [ih_body, ih_loop]
            | _ =>
              rw [h_body] at h_eval
              contradiction
          | false =>
            simp_all
        | _ =>
          rw [h_g] at h_eval
          contradiction

/-
  HINT: Remember that we have already proven `exp_eval_matches_semantics` and
  you can use that theorem in this proof, along with `clocked_eval.monotone`
  that we proved above. When using `clocked_eval.monotone` and `exists`, watch
  out for "off by one" errors that make the proof impossible. -/
theorem stmt_eval_matches_semantics
  {σ₁ σ₂ : State} {s : Stmt}
  : BigstepS σ₁ s σ₂ → ∃ n, clocked_eval σ₁ n s = (.normal σ₂)
:= by
  intro h 
  induction h with
  | skip =>
    exists 1

  | assign h_exp _ h_eq =>
    exists 1
    have h_eval := exp_eval_matches_semantics h_exp
    simp only [clocked_eval, h_eval, h_eq]

  | seq h₁ h₂ ih₁ ih₂ =>
    have ⟨n₁, h_n₁⟩ := ih₁
    have ⟨n₂, h_n₂⟩ := ih₂
    let n := n₁ + n₂
    exists n + 1
    have h₁' := clocked_eval.monotone n h_n₁ (by lia)
    have h₂' := clocked_eval.monotone n h_n₂ (by lia)
    simp [clocked_eval, h₁', h₂']

  | ifelse_tt h_guard h_body ih
  | ifelse_ff h_guard h_body ih =>
    have ⟨n, h_n⟩ := ih
    exists n + 1
    have h' := clocked_eval.monotone n h_n (by lia)
    have h_eval := exp_eval_matches_semantics h_guard
    simp [clocked_eval, h_eval, h']

  | whiledo_tt h_guard _ _ ih₁ ih₂ =>
    have ⟨n₁, h_n₁⟩ := ih₁
    have ⟨n₂, h_n₂⟩ := ih₂
    let n := n₁ + n₂
    exists n + 1
    have h₁' := clocked_eval.monotone n h_n₁ (by lia)
    have h₂' := clocked_eval.monotone n h_n₂ (by lia)
    have h_eval := exp_eval_matches_semantics h_guard
    simp [clocked_eval, h_eval, h₁', h₂']

  | whiledo_ff h_guard =>
    exists 1
    have h_eval := exp_eval_matches_semantics h_guard
    simp only [clocked_eval, h_eval]

/-
  HINT: Remember that we have already proven `exp_semantics_matches_eval` and
  you can use that theorem in this proof. Remember about `generalizing` if the
  induction hypothesis needs to be strengthened. -/
theorem stmt_semantics_matches_eval
  {σ₁ σ₂ : State} {s : Stmt}
  : (∃ n, clocked_eval σ₁ n s = (.normal σ₂)) → BigstepS σ₁ s σ₂
:= by
  intro ⟨n, h_eval⟩
  induction n generalizing σ₁ σ₂ s with
  | zero =>
    simp_all [clocked_eval]
  | succ n ih =>
    cases s with
    | skip =>
      simp_all [clocked_eval]
      subst h_eval
      exact BigstepS.skip σ₁

    | assign x rhs =>
      simp_all [clocked_eval]
      split at h_eval <;> try contradiction
      rename_i hv
      injection h_eval with h_eq
      have h_exp : BigstepE σ₁ rhs (Exp.eval σ₁ rhs) := exp_semantics_matches_eval rfl hv
      exact BigstepS.assign h_exp hv h_eq.symm 

    | seq s₁ s₂ =>
      simp_all [clocked_eval]
      cases h_s₁ : clocked_eval σ₁ n s₁ with
      | normal σ' =>
        rw [h_s₁] at h_eval
        have ih₁ := ih h_s₁
        have ih₂ := ih h_eval
        exact BigstepS.seq ih₁ ih₂
      | _ =>
        rw [h_s₁] at h_eval
        contradiction

    | ifelse guard tt ff =>
      simp_all [clocked_eval]
      cases h_guard : Exp.eval σ₁ guard with
      | bool b =>
        cases b with
        | true =>
          rw [h_guard] at h_eval
          simp at h_eval
          have ih_tt := ih h_eval
          have h_exp : BigstepE σ₁ guard (.bool true) := 
            exp_semantics_matches_eval h_guard.symm (by intro; contradiction)
          exact BigstepS.ifelse_tt h_exp ih_tt
        | false =>
          rw [h_guard] at h_eval
          simp at h_eval
          have ih_ff := ih h_eval
          have h_exp : BigstepE σ₁ guard (.bool false) := 
            exp_semantics_matches_eval h_guard.symm (by intro; contradiction)
          exact BigstepS.ifelse_ff h_exp ih_ff
      | _ =>
        rw [h_guard] at h_eval
        contradiction

    | whiledo guard body =>
      simp_all [clocked_eval]
      cases h_guard : Exp.eval σ₁ guard with
      | bool b =>
        cases b with
        | true =>
          rw [h_guard] at h_eval
          simp at h_eval
          cases h_body : clocked_eval σ₁ n body with
          | normal σ' =>
            rw [h_body] at h_eval
            have ih_body := ih h_body
            have ih_loop := ih h_eval
            have h_e : BigstepE σ₁ guard (.bool true) := exp_semantics_matches_eval h_guard.symm (by intro; contradiction)
            exact BigstepS.whiledo_tt h_e ih_body ih_loop
          | _ =>
            rw [h_body] at h_eval
            contradiction
        | false =>
          rw [h_guard] at h_eval
          simp at h_eval
          subst h_eval
          have h_exp : BigstepE σ₁ guard (.bool false) := 
            exp_semantics_matches_eval h_guard.symm (by intro; contradiction)
          exact BigstepS.whiledo_ff h_exp
      | _ =>
        rw [h_guard] at h_eval
        contradiction
