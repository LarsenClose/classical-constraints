/-
  ClassicalConstraints/Descent.lean
  Solver as section of the solution bundle.
  Factoring through a basis = descent through a quotient.

  The key formalization:
  SAT solving is a section problem.
  Low-complexity solving is a descent problem through restricted quotients.
-/

import ClassicalConstraints.Chain1_SAT.Basis
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.WellFoundedSet

/-! # Descent

A solver is a section of the solution bundle: for each satisfiable
instance, it picks a valid witness.

A solver "descends through a basis" if its witness choice depends
only on the basis profile of the instance — not on the full instance.

The central theorem family: for hard instance families, no
polynomial-grade basis admits descent of a sound section. -/

/-- A solver for an instance family: picks a witness for each
    satisfiable instance. This IS a section of the solution bundle. -/
structure Solver (F : InstanceFamily) (n : Nat) where
  /-- The witness selection function -/
  select : F.X n → F.W n
  /-- Soundness: selected witness is valid for satisfiable instances -/
  h_sound : ∀ (φ : F.X n), F.Satisfiable n φ → F.Sat n φ (select φ)

/-- A solver descends through a basis if its output is determined
    by the basis profile alone. This is the factorization condition. -/
structure DescentWitness (F : InstanceFamily)
    [alg : GradedObservableAlgebra F] (g n : Nat) where
  /-- The basis through which the solver factors -/
  basis : ObservableBasis F g n
  /-- The decoder: reconstructs witness from basis profile -/
  decode : (Fin basis.width → Nat) → F.W n
  /-- Soundness: decoded witness is valid for satisfiable instances -/
  h_sound : ∀ (φ : F.X n), F.Satisfiable n φ →
    F.Sat n φ (decode (basis.observe φ))

/-- The critical grade: minimal g such that a descent witness exists
    at size n. This is D_c — the constructive critical dimension. -/
noncomputable def criticalGrade (F : InstanceFamily)
    [alg : GradedObservableAlgebra F] (n : Nat) : Nat :=
  sInf { g | Nonempty (DescentWitness F g n) }

/-- A family is hard at polynomial grade if no fixed polynomial
    grade suffices for descent at all sizes. -/
def HardAtPolyGrade (F : InstanceFamily)
    [alg : GradedObservableAlgebra F] : Prop :=
  ∀ g : Nat, ∃ n : Nat, IsEmpty (DescentWitness F g n)
