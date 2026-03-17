/-
  ClassicalConstraints/Obstruction.lean
  When and why descent fails.

  The obstruction: quotient cells are too coarse to support
  a uniform witness choice. Within a single equivalence class
  of the basis, there exist satisfiable instances whose witness
  requirements are INCOMPATIBLE with any single decoder output.

  This is the structural content of "the problem is hard."
-/

import ClassicalConstraints.Chain1_SAT.Descent

/-! # Descent Obstruction

The obstruction to descent has a clean combinatorial form:
if a basis equivalence class contains two satisfiable instances
whose solution sets are disjoint, then no single decoder value
can satisfy both. The basis is too coarse.

The central question: for hard SAT instances, does every
polynomial-grade basis have such "conflicting" equivalence classes? -/

/-- A witness conflict: two instances in the same basis class
    have disjoint solution sets. No single witness works for both. -/
structure WitnessConflict (F : InstanceFamily)
    [alg : GradedObservableAlgebra F] {g n : Nat}
    (B : ObservableBasis F g n) where
  /-- First instance -/
  φ₁ : F.X n
  /-- Second instance -/
  φ₂ : F.X n
  /-- Both are satisfiable -/
  h_sat₁ : F.Satisfiable n φ₁
  h_sat₂ : F.Satisfiable n φ₂
  /-- They are in the same basis equivalence class -/
  h_equiv : B.Equiv φ₁ φ₂
  /-- Their solution sets are disjoint: no w satisfies both -/
  h_disjoint : ∀ w : F.W n, ¬(F.Sat n φ₁ w ∧ F.Sat n φ₂ w)

/-- If a basis has a witness conflict, no descent witness exists
    through that basis. -/
theorem no_descent_from_conflict (F : InstanceFamily)
    [alg : GradedObservableAlgebra F] {g n : Nat}
    (B : ObservableBasis F g n)
    (hc : WitnessConflict F B) :
    ¬ ∃ (d : (Fin B.width → Nat) → F.W n),
      (∀ φ, F.Satisfiable n φ → F.Sat n φ (d (B.observe φ))) := by
  intro ⟨d, hd⟩
  have h1 := hd hc.φ₁ hc.h_sat₁
  have h2 := hd hc.φ₂ hc.h_sat₂
  rw [show B.observe hc.φ₂ = B.observe hc.φ₁ from hc.h_equiv.symm] at h2
  exact hc.h_disjoint (d (B.observe hc.φ₁)) ⟨h1, h2⟩
