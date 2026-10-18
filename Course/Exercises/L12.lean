/-
  # EXERCISES FOR `L12`

  In `L08` we extended our expression language to include statements; here we
  modify that extension to use dependent types.
-/

import Course.CourseLib
import Course.L12_DExpLang

open DExpLang

inductive DStmt where
  | skip    : DStmt
  | assign  : (x : Var) → DExp x.type_of → DStmt
  | seq     : DStmt → DStmt → DStmt
  | ifelse  : DExp Bool → DStmt → DStmt → DStmt
  | whiledo : DExp Bool → DStmt → DStmt

inductive BigstepS : DState → DStmt → DState → Prop
  | skip σ : BigstepS σ .skip σ
  | assign {σ₁ σ₂ x rhs v}:
      BigstepE σ₁ rhs v → σ₂ = σ₁.insert x v →
      BigstepS σ₁ (.assign x rhs) σ₂
  | seq {σ₁ σ₂ σ₃ s₁ s₂}:
      BigstepS σ₁ s₁ σ₂ → BigstepS σ₂ s₂ σ₃ →
      BigstepS σ₁ (.seq s₁ s₂) σ₃
  | ifelse_tt {σ₁ σ₂ g tt ff} :
      BigstepE σ₁ g true → BigstepS σ₁ tt σ₂ →
      BigstepS σ₁ (.ifelse g tt ff) σ₂
  | ifelse_ff {σ₁ σ₂ g tt ff} :
      BigstepE σ₁ g false → BigstepS σ₁ ff σ₂ →
      BigstepS σ₁ (.ifelse g tt ff) σ₂
  | whiledo_tt {σ₁ σ₂ σ₃ g body} :
      BigstepE σ₁ g true → BigstepS σ₁ body σ₂ →
      BigstepS σ₂ (.whiledo g body) σ₃ → BigstepS σ₁ (.whiledo g body) σ₃
  | whiledo_ff {σ g body} :
      BigstepE σ g false → BigstepS σ (.whiledo g body) σ

/-
  ## INSTRUCTIONS
  Fill in the `sorry` for the definition of `clocked_eval` and the theorems
  below. Feel free to add lemmas if you find them helpful.
-/

/-
  We can no longer get errors during execution, so we use an `Option` to
  indicate whether we ran out of fuel or not -/
def clocked_eval (σ : DState) (fuel : ℕ) (s : DStmt) : Option DState :=
  sorry

lemma clocked_eval.monotone
  {σ₁ σ₂ : DState} {s : DStmt} {n₁ : ℕ} (n₂ : ℕ)
  : clocked_eval σ₁ n₁ s = .some σ₂ → n₁ ≤ n₂ → clocked_eval σ₁ n₂ s = .some σ₂
:= by
  sorry

theorem stmt_eval_matches_semantics
  {σ₁ σ₂ : DState} {s : DStmt}
  : BigstepS σ₁ s σ₂ → ∃ n, clocked_eval σ₁ n s = (.some σ₂)
:= by
  sorry

theorem stmt_semantics_matches_eval
  {σ₁ σ₂ : DState} {s : DStmt}
  : (∃ n, clocked_eval σ₁ n s = (.some σ₂)) → BigstepS σ₁ s σ₂
:= by
  sorry
