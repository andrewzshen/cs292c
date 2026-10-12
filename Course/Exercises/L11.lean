/-
  # EXERCISES FOR `L11`

  We define NFA and various operations on NFA and prove their correctness. Fill
  in the `sorry` in the termination proof for `accepts.ε_closure`, in the
  definitions of `union`, `concat`, and `star`, and in the theorems below. Feel
  free to add lemmas if you think they will be helpful.
-/

import Course.CourseLib
import Course.L11_DFA_Redux

set_option linter.overlappingInstances false
set_option linter.unusedSectionVars false

open Dfa_Redux

/-
  Nondeterministic finite automata. The alphabet can be any type `α` as long as
  it is finite and nonempty. We handle `ε` transitions by using `Option` for
  labels, where `none` means `ε`; we handle nondeterminism by making the final
  codomain of the transition function a (finite) set of states.

  Notice that, unlike `Dfa`, we do _not_ have a `σ_deq_fin` field ensuring that
  `σ` has decidable equality and is a finite type. We're showing an alternate
  design choice: instead of ensuring these properties here in the data
  structure, we'll ensure it in the definitions and theorems that actually
  require it. This choice  makes the definition a bit more flexible and also
  helps avoid some complications that we'll discuss more in-depth in
  `L18_ProofAdvice::INSTANCES_ARE_NOT_UNIQUE`. The drawback is that we have to
  specify these properties in all definitions and theorems that require them
  instead of here in a single place.
-/
structure Nfa
  (α : Type) [Fintype α] [Nonempty α]
where
  σ : Type
  δ : σ → Option α → Finset σ
  start : σ
  accepting : σ → Bool

namespace Nfa

variable {α : Type} [Fintype α] [Nonempty α]

/-
  Does the NFA accept a given string -/
def accepts (M : Nfa α) [DecidableEq M.σ] [Fintype M.σ] (w : List α) : Bool :=
  /-
    We accept an input if the final set of states contains an accepting state -/
  let reached := runsto {M.start}
  let accepting := reached.filter (M.accepting ·)
  accepting.Nonempty
where
  /-
    Given an initial set of states, compute the set of states reached after
    processing the input `w` -/
  runsto (init_states : Finset M.σ) : Finset M.σ :=
    w.foldl
      (fun states a => ε_closure (states.sup (M.δ · a)))
      (ε_closure init_states)
  /-
    The ε-closure of a set of states is all states reachable via an ε-transition
    from those states -/
  ε_closure [Fintype M.σ] (states : Finset M.σ) : Finset M.σ :=
    let next := states.sup (M.δ · none)
    let acc := next ∪ states
    if acc.card ≤ states.card then states else ε_closure (next ∪ states)
  termination_by
    (Fintype.card M.σ) - states.card
  decreasing_by
    have h1 := Finset.card_le_univ acc
    lia

/-
  Construct the union of two NFA. We use a type that directly describes the
  algorithm for computing the union of two NFAs: we add a new start state that
  has ε-transitions to the original start states of `M1` and `M2`; then for a
  state from `M1` we use `M1.δ` and for a state from `M2` we use `M2.δ`. So the
  type of states in the new machine is the disjoint union of a new state and the
  states of `M1` and the states of `M2`. -/
def union (M1 M2 : Nfa α) [DecidableEq M1.σ] [DecidableEq M2.σ] : Nfa α :=
  { σ := (Fin 1) ⊕ M1.σ ⊕ M2.σ
    /-
      The transition function determines whether the input state is the new
      start state or from `M1` or from `M2` and applies the appropriate
      transition. The new start state is connected by `ε` transitions to the
      start states of `M1` and `M2`. Remember that the final codomain is a set
      of states, and we need to lift their elements from `M1.σ` or `M2.σ` to be
      in the new state type `(Fin 1) ⊕ M1.σ ⊕ M2.σ`. `Finset.image` is a useful
      function here. -/
    δ := fun s a? => match s with
      | .inl _ => if a?.isNone then {liftM1 M1.start, liftM2 M2.start} else ∅
      | .inr s => match s with
        | .inl s => (M1.δ s a?).image (liftM1 ·)
        | .inr s => (M2.δ s a?).image (liftM2 ·)
    /- The start state is the new state we just created -/
    start := .inl 0
    /- Similar to `δ`, but for `accepting` -/
    accepting := fun s => match s with
      | .inl _ => false
      | .inr s => match s with
        | .inl s => M1.accepting s
        | .inr s => M2.accepting s
  }
where
  /- Lift states from their original type to the new state type -/
  liftM1 (s : M1.σ) := .inr (.inl s)
  liftM2 (s : M2.σ) := .inr (.inr s)

/-
  Construct the concatenation of two NFA. To concatenate `M1` and `M2` our new
  set of states is the disjoint union of `M1.δ` and `M2.δ`, and our transition
  function steps through `M1` until it reaches an accepting state and then makes
  an ε-transition to `M2.start` and starts stepping through `M2` -/
def concat (M1 M2 : Nfa α) [DecidableEq M1.σ] [DecidableEq M2.σ] : Nfa α :=
  { σ := M1.σ ⊕ M2.σ
    /-
      If the state is from `M1` use `M1.δ`, but add that if the state is
      accepting then also make an `ε` transition to `M2.start` -/
    δ := fun s a? => match s with
      | .inl s =>
        ((M1.δ s a?).image (liftM1 ·)) ∪
        (if M1.accepting s && a?.isNone then {liftM2 M2.start} else ∅)
      | .inr s => (M2.δ s a?).image (liftM2 ·)
    start := liftM1 M1.start
    accepting := fun s => match s with
      | .inl _ => false
      | .inr s => M2.accepting s
  }
where
  /- Lift states from their original type to the new state type -/
  liftM1 (s : M1.σ) := .inl s
  liftM2 (s : M2.σ) := .inr s

/-
  Construct the Kleene star of an NFA. To take the Kleene star of `M` our new
  set of states is the disjoint union of one new starting state and `M.σ`, and
  our transition function has an `ε` transition from the new start state to
  `M.start`, steps through `M.δ`, then for an accepting state has an
  `ε` transition back to the new start state -/
def star (M : Nfa α) [DecidableEq M.σ] : Nfa α :=
  { σ := (Fin 1) ⊕ M.σ
    δ := fun s a? => match s with
      | .inl _ => if a?.isNone then {liftM M.start} else ∅
      | .inr s =>
        ((M.δ s a?).image (liftM ·)) ∪
        (if M.accepting s && a?.isNone then {.inl 0} else ∅)
    start := .inl 0
    accepting := fun s => match s with
      | .inl _ => false
      | .inr s => M.accepting s
  }
where
  /- Lift states from their original type to the new state type -/
  liftM (s : M.σ) := .inr s

/-
  To prove correctness we go through a similar process as for DFA -/

variable
  (M M1 M2 : Nfa α)
  [DecidableEq M.σ] [Fintype M.σ]
  [DecidableEq M1.σ] [Fintype M1.σ]
  [DecidableEq M2.σ] [Fintype M2.σ]

inductive RunsTo (M : Nfa α) : M.σ → List α → M.σ → Prop where
  | refl σ₁ : M.RunsTo σ₁ [] σ₁
  | eps {σ₁ σ₂ σ₃ w} : M.RunsTo σ₁ w σ₂ → σ₃ ∈ M.δ σ₂ none → M.RunsTo σ₁ w σ₃
  | step {σ₁ σ₂ σ₃ w a} : M.RunsTo σ₁ w σ₂ → σ₃ ∈ M.δ σ₂ (.some a) →
      M.RunsTo σ₁ (w ++ [a]) σ₃

def accepts_prop (M : Nfa α) (w : List α) : Prop :=
  ∃ σ, M.RunsTo M.start w σ ∧ M.accepting σ

def L (M : Nfa α) : Language α :=
  { w | M.accepts_prop w }

attribute [simp] RunsTo.refl
attribute [simp] RunsTo.eps
attribute [simp] RunsTo.step
attribute [simp] accepts_prop
attribute [simp] L

/-
  When we proved theorems about DFA in `L09_DFA_Redux` we proved the equivalence
  of `RunsTo` and `runsto` and then rewrote everything in terms of `runsto`
  because it was easier to prove things with (since it is implemented with a
  very simple foldl and Mathlib has a bunch of theorems about foldl already).
  For NFA, however, the implementation of `runsto` is much more complicated and
  difficult to reason about, including a recursive fixpoint computation for
  `ε_closure`. We'll want to do the opposite and (once we've proven `RunsTo` and
  `runsto` are equivalent) rewrite everything in terms of `RunsTo` in later
  proofs. Doing so means that we need to prove various lemmas about `RunsTo`
  that we didn't need to prove for DFA, however this will ultimately make the
  proofs easier because we don't have to reason about the `runsto`
  implementation (except for proving equivalence to `RunsTo`, of course). -/
namespace RunsTo

lemma eps_closure_complete
  (σ₁ σ₂ : M.σ) (S : Finset M.σ)
  : σ₁ ∈ accepts.ε_closure M S → σ₂ ∈ M.δ σ₁ none → σ₂ ∈ accepts.ε_closure M S
:= by
  sorry

lemma eps_closure_monotone
  (σ : M.σ) (S : Finset M.σ)
  : σ ∈ S → σ ∈ accepts.ε_closure M S
:= by
  sorry

lemma runsto_equiv
  {σ₁ σ₂ : M.σ} {w : List α}
  : σ₂ ∈ accepts.runsto M w {σ₁} ↔ M.RunsTo σ₁ w σ₂
:= by
  sorry

/-
  HINT: we're trying to prove something that relies on two premises (`RunsTo` on
  `w₁` and `RunsTo` on `w₂`). We need the information from both, but we can only
  do rule induction on one of them. Since `RunsTo` is defined by appending
  elements, the best approach is to uses `cases` on the first `RunsTo`, then
  induction on the second. -/
lemma runsto_trans
  {M : Nfa α} {σ₁ σ₂ σ₃ : M.σ} {w₁ w₂ : List α}
  : M.RunsTo σ₁ w₁ σ₂ → M.RunsTo σ₂ w₂ σ₃ → M.RunsTo σ₁ (w₁ ++ w₂) σ₃
:= by
  sorry

end RunsTo

/- ----- accepts_is_correct ----- -/

theorem accepts_is_correct
  {w : List α}
  : M.accepts_prop w ↔ M.accepts w
:= by
  sorry

/- ----- union_is_correct ----- -/

theorem union_is_correct : M1.L ∪ M2.L = (M1.union M2).L := by
  sorry

/- ----- concat_is_correct ----- -/

/-
  `simp` can't see "underneath" our `*` notation for `Language` concatenation.
  The standard way to handle this is to prove a lemma by `rfl`, and make the
  lemma available to `simp` via annotation. -/
@[simp]
lemma lang_mul_eq_append {L₁ L₂ : Language α} {w : List α}
  : w ∈ L₁ * L₂ ↔ w ∈ Set.image2 (· ++ ·) L₁ L₂
:= by rfl

theorem concat_is_correct : M1.L * M2.L = (M1.concat M2).L := by
  sorry

/- ----- star_is_correct ----- -/

theorem star_is_correct : kleene_star M.L = M.star.L := by
  sorry

end Nfa
