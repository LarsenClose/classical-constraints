/-
  ClassicalConstraints/Chain4_CSP/BridgeVacuity.lean
  CSPTransferHypothesis is uninhabitable in TC models.

  The lock theorem (no_poly_csp_solver_via_transfer) takes SelfAppUnbounded,
  CSPTransferHypothesis, a CSPInstance, and a PolyTimeCSPSolver, and derives False.
  This file proves that CSPTransferHypothesis + SelfAppUnbounded
  already gives False -- the solver and instance hypotheses are redundant,
  and the lock theorem is vacuously true.

  The proof: BoundedAlgebraicWitness always exists (empty essential_vars).
  CSPTransferHypothesis maps any bounded witness to a grade-bounded
  function agreeing with selfApp. Side A says no such function
  exists when selfApp is unbounded. Contradiction.

  STATUS: 0 sorry, 0 Classical.choice.
-/

import ClassicalConstraints.Chain4_CSP.CSPAlgebraLock

namespace ClassicalConstraints

-- ════════════════════════════════════════════════════════════
-- Section 1: Trivial CSP instance and bounded witness
-- ════════════════════════════════════════════════════════════

/-- A trivial CSP instance with 0 variables and no constraints.
    Any constraint language admits such an instance. -/
def trivialCSPInstance (dom : CSPDomain) (lang : ConstraintLanguage dom) :
    CSPInstance dom lang where
  num_vars := 0
  constraints := []

/-- A trivial bounded algebraic witness exists for any CSP instance at any
    capacity. The input type of CSPTransferHypothesis.transfer is
    always inhabited. -/
def trivialBoundedAlgebraicWitness (dom : CSPDomain) (lang : ConstraintLanguage dom)
    (inst : CSPInstance dom lang) (d : Nat) :
    BoundedAlgebraicWitness dom lang inst d where
  essential_vars := ∅
  bounded := by simp

-- ════════════════════════════════════════════════════════════
-- Section 2: CSPTransferHypothesis is uninhabitable in TC models
-- ════════════════════════════════════════════════════════════

/-- CSPTransferHypothesis is uninhabitable when SelfAppUnbounded holds.

    Proof: construct a trivial bounded algebraic witness at capacity 0,
    apply the transfer to get a grade-0-bounded function agreeing
    with selfApp on grade-0 inputs, contradict Side A.

    The solver and instance hypotheses in no_poly_csp_solver_via_transfer
    are redundant. The contradiction comes from CSPTransferHypothesis +
    SelfAppUnbounded alone. -/
theorem csp_transfer_hypothesis_uninhabitable
    (M : GradedReflModel_Mirror)
    (hub : SelfAppUnbounded_Mirror M)
    (dom : CSPDomain)
    (lang : ConstraintLanguage dom)
    (tr : CSPTransferHypothesis M dom lang) :
    False := by
  let inst := trivialCSPInstance dom lang
  let wit := trivialBoundedAlgebraicWitness dom lang inst 0
  obtain ⟨f, hbound, hagree⟩ := tr.transfer inst 0 wit
  exact sideA_bounded_selector_impossible M hub 0
    ⟨f, hagree, fun x _ => hbound x⟩

end ClassicalConstraints
