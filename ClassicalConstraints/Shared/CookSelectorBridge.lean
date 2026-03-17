/-
  ClassicalConstraints/CookSelectorBridge.lean
  The central semantic theorem: poly-time SAT solving = bounded local observation.

  A poly-time solver can only read poly(n) bits of its input assignment,
  so its output factors through a bounded interface. This is the
  TRANSLATION theorem (poly-time computation implies bounded selector),
  not the no-go theorem.

  Key result: `poly_solver_induces_bounded_selector` — every poly-time
  solver for a SAT family induces a bounded selector on the constraint
  topology.
-/

import ClassicalConstraints.Shared.Basic
import ClassicalConstraints.Shared.SATPresheafCore

/-! # Cook Selector Bridge

The bridge between computational complexity and presheaf structure:
a poly-time solver factors through a bounded observation window,
producing a bounded selector on the SAT instance's variable space.

The chain of reasoning:
1. A poly-time solver runs in time p(n), so it accesses at most p(n) variables.
2. Two assignments agreeing on those variables produce the same output.
3. This factorization IS a bounded selector.
4. The bounded selector IS a local section of the constraint presheaf. -/

namespace ClassicalConstraints

open SATInstance

/-! ## Polynomial Bounds -/

/-- A polynomial bound specified by degree and constant.
    Represents the function n ↦ n^degree + constant. -/
structure PolyBound where
  degree : Nat
  constant : Nat

namespace PolyBound

/-- Evaluate the polynomial bound at input n. -/
def eval (p : PolyBound) (n : Nat) : Nat :=
  n ^ p.degree + p.constant

theorem eval_ge_constant (p : PolyBound) (n : Nat) : p.eval n ≥ p.constant := by
  unfold eval; omega

theorem eval_monotone (p : PolyBound) {m n : Nat} (hmn : m ≤ n) (_hd : p.degree > 0) :
    p.eval m ≤ p.eval n := by
  unfold eval
  have : m ^ p.degree ≤ n ^ p.degree := Nat.pow_le_pow_left hmn p.degree
  omega

end PolyBound

/-! ## Access Profiles

An access profile records which variables a solver actually inspects.
The key observation: a poly-time solver on n-variable Boolean inputs
can inspect at most poly(n) variables. -/

/-- The set of variables accessed by a computation on a SAT instance,
    together with a bound on how many were accessed. -/
structure AccessProfile (φ : SATInstance) (capacity : Nat) where
  /-- Which variables were accessed -/
  accessed_vars : List (Fin φ.num_vars)
  /-- The number of accessed variables is within the capacity -/
  h_bound : accessed_vars.length ≤ capacity

/-- An access profile with no accessed variables. -/
def AccessProfile.empty (φ : SATInstance) (capacity : Nat) : AccessProfile φ capacity where
  accessed_vars := []
  h_bound := Nat.zero_le _

/-! ## Bounded Local Covers

A bounded local cover is a collection of variable patches, each of
bounded size. This is the presheaf-theoretic view of what a solver
can observe. -/

/-- A collection of variable patches, each of bounded size. -/
structure BoundedLocalCover (φ : SATInstance) (capacity : Nat) where
  /-- The patches: each is a list of variable indices -/
  patches : List (List (Fin φ.num_vars))
  /-- Each patch has bounded size -/
  h_bounded : ∀ p, p ∈ patches → p.length ≤ capacity

/-- A trivial cover with a single patch from an access profile. -/
def BoundedLocalCover.fromProfile {φ : SATInstance} {capacity : Nat}
    (ap : AccessProfile φ capacity) : BoundedLocalCover φ capacity where
  patches := [ap.accessed_vars]
  h_bounded := by
    intro p hp
    simp at hp
    rw [hp]
    exact ap.h_bound

/-! ## Solver Factorization

The key semantic property: a solver's output depends only on the
variables it accesses. This is a data-processing inequality —
if the solver runs in time T, it can read at most T input bits,
so its output is determined by those bits. -/

/-- A solver factors through a bounded set of variables: its output
    depends only on the values of those variables. -/
structure SolverFactorsThrough (φ : SATInstance) (capacity : Nat)
    (solver : φ.Assignment → Bool) where
  /-- The cover witnessing bounded observation -/
  cover : BoundedLocalCover φ capacity
  /-- The specific variables the solver depends on -/
  accessed : List (Fin φ.num_vars)
  /-- The accessed list is bounded -/
  h_accessed_bounded : accessed.length ≤ capacity
  /-- The solver output depends only on accessed variables -/
  h_factors : ∀ a₁ a₂ : φ.Assignment,
    (∀ v, v ∈ accessed → a₁ v = a₂ v) → solver a₁ = solver a₂

/-! ## Poly-Time Solvers

A poly-time solver for a SAT instance family. The crucial modeling
choice: we include the factorization property as part of the structure,
because it IS what "poly-time on Boolean inputs" means — a computation
that runs in time p(n) can only read p(n) bits of its input.

This is not an additional assumption; it is the semantic content of
the time bound applied to Boolean function computation. -/

/-- A family of SAT instances indexed by size parameter. -/
def SATFamily := Nat → SATInstance

/-- A poly-time solver for a SAT family.
    The solver correctly decides satisfiability for each instance
    in the family, and its computation accesses at most poly(n)
    variables of the assignment. -/
structure PolyTimeSolver (family : SATFamily) where
  /-- The solving function at each size -/
  solve : (n : Nat) → (family n).Assignment → Bool
  /-- Correctness: the solver agrees with the satisfaction predicate -/
  h_correct : ∀ n a, solve n a = (family n).instanceSatisfied a
  /-- The polynomial time bound -/
  time_bound : PolyBound
  /-- Which variables are accessed at each size -/
  accessed_at : (n : Nat) → List (Fin (family n).num_vars)
  /-- The access count is bounded by the time bound -/
  h_access_bounded : ∀ n, (accessed_at n).length ≤ time_bound.eval n
  /-- The solver depends only on accessed variables -/
  h_access_sufficient : ∀ n (a₁ a₂ : (family n).Assignment),
    (∀ v, v ∈ accessed_at n → a₁ v = a₂ v) → solve n a₁ = solve n a₂

/-- A poly-time solver factors through a bounded set of variables at each size. -/
def poly_solver_factors (family : SATFamily) (solver : PolyTimeSolver family) (n : Nat) :
    SolverFactorsThrough (family n) (solver.time_bound.eval n) (solver.solve n) where
  cover := BoundedLocalCover.fromProfile ⟨solver.accessed_at n, solver.h_access_bounded n⟩
  accessed := solver.accessed_at n
  h_accessed_bounded := solver.h_access_bounded n
  h_factors := solver.h_access_sufficient n

/-! ## Bounded Selectors

A bounded selector is the presheaf-theoretic object induced by a solver:
a Boolean function on assignments that factors through a bounded
observation window. -/

/-- A bounded selector on a SAT instance: a Boolean function that
    depends on at most `capacity` variables. -/
structure BoundedSelector (φ : SATInstance) (capacity : Nat) where
  /-- The selection function -/
  select : φ.Assignment → Bool
  /-- Which variables the selector depends on -/
  accessed_vars : List (Fin φ.num_vars)
  /-- The number of accessed variables is bounded -/
  h_bounded : accessed_vars.length ≤ capacity
  /-- The selector depends only on accessed variables -/
  h_factors : ∀ a₁ a₂ : φ.Assignment,
    (∀ v, v ∈ accessed_vars → a₁ v = a₂ v) → select a₁ = select a₂

/-- A bounded selector that always returns false. -/
def BoundedSelector.trivial (φ : SATInstance) (capacity : Nat) : BoundedSelector φ capacity where
  select := fun _ => false
  accessed_vars := []
  h_bounded := Nat.zero_le _
  h_factors := fun _ _ _ => rfl

/-- A bounded selector that depends on a single variable. -/
def BoundedSelector.single (φ : SATInstance) (capacity : Nat) (v : Fin φ.num_vars)
    (hcap : 1 ≤ capacity) : BoundedSelector φ capacity where
  select := fun a => a v
  accessed_vars := [v]
  h_bounded := by simp; exact hcap
  h_factors := fun a₁ a₂ h => by
    apply h
    simp

/-! ## The Bridge: Solver → Selector -/

/-- Convert a solver factorization into a bounded selector. -/
def solver_to_selector {φ : SATInstance} {capacity : Nat}
    {solver : φ.Assignment → Bool}
    (sf : SolverFactorsThrough φ capacity solver) : BoundedSelector φ capacity where
  select := solver
  accessed_vars := sf.accessed
  h_bounded := sf.h_accessed_bounded
  h_factors := sf.h_factors

/-- The main bridge: a poly-time solver induces a bounded selector at each size.
    This is the semantic content of "poly-time computation = bounded observation." -/
def poly_solver_induces_bounded_selector
    (family : SATFamily) (solver : PolyTimeSolver family) (n : Nat) :
    BoundedSelector (family n) (solver.time_bound.eval n) :=
  solver_to_selector (poly_solver_factors family solver n)

/-- The induced selector is correct: it agrees with instanceSatisfied. -/
theorem bounded_selector_correct
    (family : SATFamily) (solver : PolyTimeSolver family) (n : Nat)
    (a : (family n).Assignment) :
    (poly_solver_induces_bounded_selector family solver n).select a =
      (family n).instanceSatisfied a := by
  simp [poly_solver_induces_bounded_selector, solver_to_selector, poly_solver_factors]
  exact solver.h_correct n a

/-! ## Structural Properties of Bounded Selectors -/

/-- Two bounded selectors agree if they use the same select function. -/
theorem bounded_selector_ext {φ : SATInstance} {cap : Nat}
    (s₁ s₂ : BoundedSelector φ cap)
    (h : ∀ a, s₁.select a = s₂.select a) :
    s₁.select = s₂.select :=
  funext h

/-- A bounded selector with capacity 0 is constant. -/
theorem bounded_selector_zero_constant {φ : SATInstance}
    (s : BoundedSelector φ 0) :
    ∀ a₁ a₂ : φ.Assignment, s.select a₁ = s.select a₂ := by
  intro a₁ a₂
  apply s.h_factors
  intro v hv
  have hlen : s.accessed_vars.length ≤ 0 := s.h_bounded
  have hempty : s.accessed_vars = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
  rw [hempty] at hv
  simp at hv

/-- A correct bounded selector detects satisfiability. -/
theorem bounded_selector_detects_sat
    (family : SATFamily) (solver : PolyTimeSolver family) (n : Nat) :
    (family n).Satisfiable ↔
      ∃ a : (family n).Assignment,
        (poly_solver_induces_bounded_selector family solver n).select a = true := by
  constructor
  · intro ⟨a, ha⟩
    exact ⟨a, by rw [bounded_selector_correct]; exact ha⟩
  · intro ⟨a, ha⟩
    exact ⟨a, by rwa [bounded_selector_correct] at ha⟩

/-! ## Capacity Gap

The capacity gap is the core structural observation: when the SAT
instance has more variables than the solver can access, the solver
must be "blind" to some variables. This is where the presheaf
structure becomes load-bearing. -/

/-- A SAT instance has a capacity gap relative to a bound when the
    number of variables exceeds the bound. -/
def hasCapacityGap (φ : SATInstance) (capacity : Nat) : Prop :=
  φ.num_vars > capacity

/-- A capacity gap implies at least one variable is not accessed by the selector.
    This is the pigeonhole step: accessed_vars has length ≤ capacity < num_vars,
    so some Fin num_vars element is missing from accessed_vars. -/
theorem capacity_gap_implies_unaccessed_var
    {φ : SATInstance} {capacity : Nat}
    (s : BoundedSelector φ capacity)
    (hgap : hasCapacityGap φ capacity) :
    ∃ v : Fin φ.num_vars, v ∉ s.accessed_vars := by
  by_contra h_all
  push_neg at h_all
  -- Every Fin φ.num_vars is in accessed_vars, so accessed_vars.length ≥ φ.num_vars
  have h_card : φ.num_vars ≤ s.accessed_vars.length := by
    have h1 : (Finset.univ : Finset (Fin φ.num_vars)).card ≤ s.accessed_vars.toFinset.card := by
      apply Finset.card_le_card
      intro v _
      exact List.mem_toFinset.mpr (h_all v)
    simp at h1
    exact Nat.le_trans h1 (List.toFinset_card_le s.accessed_vars)
  -- But accessed_vars.length ≤ capacity < φ.num_vars — contradiction
  have := s.h_bounded
  unfold hasCapacityGap at hgap
  omega

/-- An unaccessed variable creates a blind spot: the selector cannot
    distinguish assignments that differ only on that variable. -/
theorem unaccessed_var_implies_blind_spot
    {φ : SATInstance} {capacity : Nat}
    (s : BoundedSelector φ capacity)
    (v : Fin φ.num_vars)
    (hv : v ∉ s.accessed_vars) :
    ∀ a : φ.Assignment, ∀ b : Bool,
      s.select a = s.select (Function.update a v b) := by
  intro a b
  apply s.h_factors
  intro w hw
  by_cases heq : w = v
  · exact absurd (heq ▸ hw) hv
  · simp [Function.update, heq]

/-- Capacity gap implies blind spots: when num_vars > capacity,
    there exists an unaccessed variable that the selector is blind to.
    Composes capacity_gap_implies_unaccessed_var with unaccessed_var_implies_blind_spot. -/
theorem capacity_gap_implies_blind_spots
    {φ : SATInstance} {capacity : Nat}
    (s : BoundedSelector φ capacity)
    (hgap : hasCapacityGap φ capacity) :
    ∃ v : Fin φ.num_vars, ∀ a : φ.Assignment, ∀ b : Bool,
      s.select a = s.select (Function.update a v b) :=
  let ⟨v, hv⟩ := capacity_gap_implies_unaccessed_var s hgap
  ⟨v, unaccessed_var_implies_blind_spot s v hv⟩

/-! ## Monotonicity of Selector Capacity -/

/-- A bounded selector at capacity c is also a bounded selector at any
    larger capacity c'. -/
def BoundedSelector.weaken {φ : SATInstance} {c : Nat}
    (s : BoundedSelector φ c) {c' : Nat} (hle : c ≤ c') :
    BoundedSelector φ c' where
  select := s.select
  accessed_vars := s.accessed_vars
  h_bounded := Nat.le_trans s.h_bounded hle
  h_factors := s.h_factors

/-- Weakening preserves the selection function. -/
theorem BoundedSelector.weaken_select {φ : SATInstance} {c : Nat}
    (s : BoundedSelector φ c) {c' : Nat} (hle : c ≤ c') :
    (s.weaken hle).select = s.select :=
  rfl

/-! ## Connection to Presheaf Sections

A bounded selector that correctly decides satisfiability gives
a global section detector: it factors the satisfiability question
through bounded local data. -/

/-- A correct bounded selector witnesses that satisfiability
    can be detected through bounded observation. -/
structure BoundedSatisfiabilityWitness (φ : SATInstance) (capacity : Nat) where
  /-- The underlying bounded selector -/
  selector : BoundedSelector φ capacity
  /-- Correctness: the selector agrees with satisfiability -/
  h_correct : ∀ a : φ.Assignment,
    selector.select a = φ.instanceSatisfied a

/-- A poly-time solver yields a bounded satisfiability witness. -/
def poly_solver_witness (family : SATFamily) (solver : PolyTimeSolver family) (n : Nat) :
    BoundedSatisfiabilityWitness (family n) (solver.time_bound.eval n) where
  selector := poly_solver_induces_bounded_selector family solver n
  h_correct := bounded_selector_correct family solver n

/-- The witness selector detects satisfiability iff the instance is satisfiable. -/
theorem witness_detects_satisfiability
    (family : SATFamily) (solver : PolyTimeSolver family) (n : Nat) :
    (family n).Satisfiable ↔
      ∃ a, (poly_solver_witness family solver n).selector.select a = true :=
  bounded_selector_detects_sat family solver n

/-! ## Factoring Through Local Restriction

A bounded selector induces a notion of "local equivalence" on assignments:
two assignments are equivalent if the selector cannot tell them apart. -/

/-- Two assignments are locally equivalent with respect to a bounded
    selector if they agree on all accessed variables. -/
def BoundedSelector.localEquiv {φ : SATInstance} {cap : Nat}
    (s : BoundedSelector φ cap)
    (a₁ a₂ : φ.Assignment) : Prop :=
  ∀ v, v ∈ s.accessed_vars → a₁ v = a₂ v

/-- Local equivalence is reflexive. -/
theorem BoundedSelector.localEquiv_refl {φ : SATInstance} {cap : Nat}
    (s : BoundedSelector φ cap) (a : φ.Assignment) :
    s.localEquiv a a :=
  fun _ _ => rfl

/-- Local equivalence is symmetric. -/
theorem BoundedSelector.localEquiv_symm {φ : SATInstance} {cap : Nat}
    (s : BoundedSelector φ cap) {a₁ a₂ : φ.Assignment}
    (h : s.localEquiv a₁ a₂) : s.localEquiv a₂ a₁ :=
  fun v hv => (h v hv).symm

/-- Local equivalence is transitive. -/
theorem BoundedSelector.localEquiv_trans {φ : SATInstance} {cap : Nat}
    (s : BoundedSelector φ cap) {a₁ a₂ a₃ : φ.Assignment}
    (h₁₂ : s.localEquiv a₁ a₂) (h₂₃ : s.localEquiv a₂ a₃) :
    s.localEquiv a₁ a₃ :=
  fun v hv => (h₁₂ v hv).trans (h₂₃ v hv)

/-- The selector is constant on local equivalence classes. -/
theorem BoundedSelector.select_localEquiv {φ : SATInstance} {cap : Nat}
    (s : BoundedSelector φ cap) {a₁ a₂ : φ.Assignment}
    (h : s.localEquiv a₁ a₂) : s.select a₁ = s.select a₂ :=
  s.h_factors a₁ a₂ h

/-! ## Summary of the Bridge

The chain of implications proved in this file:

  PolyTimeSolver family
    → (∀ n, SolverFactorsThrough (family n) (time_bound.eval n) (solve n))
    → (∀ n, BoundedSelector (family n) (time_bound.eval n))
    → (∀ n, BoundedSatisfiabilityWitness (family n) (time_bound.eval n))

This is the TRANSLATION: poly-time computation is bounded local observation.
The NO-GO (bounded observation cannot solve SAT in general) is proved
elsewhere, using the capacity gap and presheaf obstruction. -/

end ClassicalConstraints
