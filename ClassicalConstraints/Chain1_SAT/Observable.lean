/-
  ClassicalConstraints/Observable.lean
  Graded observable language.

  CRITICAL DESIGN CHOICE:
  The observable basis must be TYPED BY GRADE, not arbitrary poly-time.
  If basis is allowed to be an arbitrary polynomial-time family of
  features, it can encode the solver's own computation trace, and
  "selection basis" says nothing.

  So we define observables as an inductive graded family:
  - Grade 0: raw local predicates on instances
  - Grade k+1: bounded compositions of grade-k observables
  The grade controls the "depth of correlation" the observable can see.
-/

import Mathlib.Data.Fintype.Basic
import ClassicalConstraints.Shared.Basic

/-! # Graded Observables

An observable at grade g on instances of size n is a function
X n → Fin k for some finite codomain, built by allowed constructors
from lower-grade observables.

The grade is NOT arbitrary computational complexity.
It is structural depth: how many levels of composition
are needed to define the observable. -/

/-- A graded observable algebra over an instance family.

  This is kept abstract deliberately. The specific constructors
  (what counts as a grade-0 observable, how composition works)
  are parameters of the theory, not fixed definitions.

  Different instantiations give different notions of "bounded
  observation." The theorems should hold for ANY reasonable
  graded observable algebra satisfying the axioms below. -/
class GradedObservableAlgebra (F : InstanceFamily) where
  /-- The type of observables at grade g on instances of size n -/
  Obs : (g : Nat) → (n : Nat) → Type
  /-- Each observable induces a function on instances -/
  eval : {g n : Nat} → Obs g n → F.X n → Nat
  /-- Observables have finite range -/
  h_fin_range : ∀ g n (o : Obs g n), ∃ k : Nat, ∀ x, eval o x < k
  /-- Grade 0 observables exist (raw predicates) -/
  h_base : ∀ n, Nonempty (Obs 0 n)
  /-- Lower grade embeds into higher grade (monotonicity) -/
  embed : {g n : Nat} → Obs g n → Obs (g + 1) n
  /-- Embedding preserves semantics -/
  h_embed : ∀ {g n} (o : Obs g n) (x : F.X n),
    eval (embed o) x = eval o x
  /-- The range of grade-g observables is polynomially bounded in n -/
  h_poly_range : ∀ g, ∃ c : Nat, ∀ n (o : Obs g n) (x : F.X n),
    eval o x < n ^ g + c


