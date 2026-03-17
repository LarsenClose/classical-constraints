/-
  ClassicalConstraints/Basis.lean
  Observable basis as graded quotient of instance space.

  A basis is a finite tuple of observables from a graded algebra.
  It induces a quotient of instance space: two instances are
  equivalent if they agree on all basis observables.

  A solver "factors through a basis" if its output depends only
  on the equivalence class — i.e., instances that look the same
  to the basis get the same witness.
-/

import ClassicalConstraints.Chain1_SAT.Observable

/-! # Observable Basis

The basis is the "selection function's vocabulary" — what it
can see about an instance. The grade bounds how deep the
correlations it can track. The cardinality bounds how many
distinctions it can make. -/

/-- A finite collection of grade-g observables forming a basis. -/
structure ObservableBasis (F : InstanceFamily)
    [alg : GradedObservableAlgebra F] (g : Nat) (n : Nat) where
  /-- Number of observables in the basis -/
  width : Nat
  /-- The observables themselves -/
  obs : Fin width → alg.Obs g n

namespace ObservableBasis

variable {F : InstanceFamily} [alg : GradedObservableAlgebra F]
  {g n : Nat}

/-- The observation map: project an instance to its basis profile.
    Two instances with the same profile are indistinguishable
    to any selector using this basis. -/
def observe (B : ObservableBasis F g n) (φ : F.X n) : Fin B.width → Nat :=
  fun i => alg.eval (B.obs i) φ

/-- Two instances are basis-equivalent if they have the same profile. -/
def Equiv (B : ObservableBasis F g n) (φ₁ φ₂ : F.X n) : Prop :=
  B.observe φ₁ = B.observe φ₂

/-- Basis equivalence is an equivalence relation. -/
theorem equiv_is_equiv (B : ObservableBasis F g n) :
    Equivalence (B.Equiv) where
  refl := fun _ => rfl
  symm := fun h => h.symm
  trans := fun h₁ h₂ => h₁.trans h₂

end ObservableBasis
