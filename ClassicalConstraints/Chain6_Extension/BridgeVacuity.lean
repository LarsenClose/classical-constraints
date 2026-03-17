/-
  ClassicalConstraints/Chain6_Extension/BridgeVacuity.lean
  GeometricTransferHypothesis is uninhabitable in TC models.

  The lock theorem (no_poly_sat_solver_geometric) takes SelfAppUnbounded,
  GeometricTransferHypothesis, and a PolyTimeSolver, and derives False.
  This file proves that GeometricTransferHypothesis + SelfAppUnbounded
  already gives False — the solver hypothesis is redundant,
  and the lock theorem is vacuously true.

  The proof: bounded selectors always exist (constant functions).
  GeometricTransferHypothesis maps any bounded selector to a grade-bounded
  function agreeing with selfApp. Side A says no such function
  exists when selfApp is unbounded. Contradiction.

  trivialSelector is reused from Chain1_SAT/BridgeVacuity.lean.

  STATUS: 0 sorry, 0 Classical.choice.
-/

import ClassicalConstraints.Chain6_Extension.ExtensionComplexityLock
import ClassicalConstraints.Chain1_SAT.BridgeVacuity

namespace ClassicalConstraints

-- ════════════════════════════════════════════════════════════
-- Section 1: GeometricTransferHypothesis is uninhabitable
-- ════════════════════════════════════════════════════════════

/-- GeometricTransferHypothesis is uninhabitable when SelfAppUnbounded holds.

    Proof: construct a trivial bounded selector at capacity 0,
    apply the geometric transfer to get a grade-0-bounded function agreeing
    with selfApp on grade-0 inputs, contradict Side A.

    The solver hypothesis in no_poly_sat_solver_geometric is redundant.
    The contradiction comes from GeometricTransferHypothesis +
    SelfAppUnbounded alone. -/
theorem geometric_transfer_hypothesis_uninhabitable
    (M : GradedReflModel_Mirror)
    (hub : SelfAppUnbounded_Mirror M)
    (family : SATFamily)
    (enc : CookEncoding)
    (cf : CookFaithful enc)
    (tr : GeometricTransferHypothesis M family enc cf) :
    False := by
  let sel := trivialSelector (family 0) 0
  obtain ⟨f, hbound, hagree⟩ := tr.transfer 0 0 sel
  exact sideA_bounded_selector_impossible M hub 0
    ⟨f, hagree, fun x _ => hbound x⟩

-- ════════════════════════════════════════════════════════════
-- Section 2: The lock theorem is vacuously true
-- ════════════════════════════════════════════════════════════

/-- The lock theorem's hypothesis set is unsatisfiable.
    No GeometricTransferHypothesis can be constructed in any model
    where SelfAppUnbounded holds. -/
theorem geometric_lock_hypothesis_unsatisfiable
    (M : GradedReflModel_Mirror)
    (hub : SelfAppUnbounded_Mirror M)
    (family : SATFamily)
    (enc : CookEncoding)
    (cf : CookFaithful enc) :
    GeometricTransferHypothesis M family enc cf → False :=
  geometric_transfer_hypothesis_uninhabitable M hub family enc cf

/-- The solver hypothesis in no_poly_sat_solver_geometric is redundant.
    The lock fires from GeometricTransferHypothesis + SelfAppUnbounded
    alone, for any solver or no solver. -/
theorem geometric_solver_hypothesis_redundant
    (M : GradedReflModel_Mirror)
    (hub : SelfAppUnbounded_Mirror M)
    (family : SATFamily)
    (enc : CookEncoding)
    (cf : CookFaithful enc)
    (tr : GeometricTransferHypothesis M family enc cf) :
    ∀ _ : PolyTimeSolver family, False :=
  fun _ => geometric_transfer_hypothesis_uninhabitable M hub family enc cf tr

-- ════════════════════════════════════════════════════════════
-- Section 3: GeometricTransferHypothesis implies grade-non-increasing
-- ════════════════════════════════════════════════════════════

/-- GeometricTransferHypothesis implies selfApp is grade-non-increasing.

    For any x, invoke the transfer at d = grade(x) with a trivial
    selector. The returned function agrees with selfApp at x and
    has grade output ≤ grade(x). Therefore grade(selfApp(x)) ≤ grade(x).

    This is strictly stronger than PEqNP. -/
theorem geometric_transfer_implies_grade_nonincreasing
    (M : GradedReflModel_Mirror)
    (family : SATFamily)
    (enc : CookEncoding)
    (cf : CookFaithful enc)
    (tr : GeometricTransferHypothesis M family enc cf) :
    ∀ x, M.grade (M.selfApp x) ≤ M.grade x := by
  intro x
  obtain ⟨f, hbound, hagree⟩ := tr.transfer 0 (M.grade x)
    (trivialSelector (family 0) (M.grade x))
  rw [← hagree x (Nat.le_refl _)]
  exact hbound x

/-- Alternative proof of uninhabitability via grade-non-increasing. -/
theorem geometric_transfer_uninhabitable_via_nonincreasing
    (M : GradedReflModel_Mirror)
    (hub : SelfAppUnbounded_Mirror M)
    (family : SATFamily)
    (enc : CookEncoding)
    (cf : CookFaithful enc)
    (tr : GeometricTransferHypothesis M family enc cf) :
    False :=
  selfApp_nonincreasing_contradiction M hub M.selfApp
    (fun _ => rfl)
    (geometric_transfer_implies_grade_nonincreasing M family enc cf tr)

-- ════════════════════════════════════════════════════════════
-- Section 4: Complete characterization
-- ════════════════════════════════════════════════════════════

/-- What GeometricTransferHypothesis actually requires of a model:
    (1) selfApp is grade-non-increasing,
    (2) selfApp factors through every grade,
    (3) PEqNP holds,
    (4) SelfAppUnbounded is impossible.

    The bridge condition is equivalent to a regime assertion.
    The "open condition" is not independent of the regime question —
    it IS the regime question. -/
theorem geometric_transfer_hypothesis_characterization
    (M : GradedReflModel_Mirror)
    (family : SATFamily)
    (enc : CookEncoding)
    (cf : CookFaithful enc)
    (tr : GeometricTransferHypothesis M family enc cf) :
    (∀ x, M.grade (M.selfApp x) ≤ M.grade x) ∧
    (∀ d, FactorsThrough_Mirror M M.selfApp d) ∧
    PEqNP_Mirror M ∧
    ¬SelfAppUnbounded_Mirror M := by
  refine ⟨
    geometric_transfer_implies_grade_nonincreasing M family enc cf tr,
    ?_,
    ?_,
    fun hub => geometric_transfer_hypothesis_uninhabitable M hub family enc cf tr⟩
  · intro d x hx
    have := geometric_transfer_implies_grade_nonincreasing M family enc cf tr x
    omega
  · exact ⟨0, fun x hx =>
      Nat.le_trans
        (geometric_transfer_implies_grade_nonincreasing M family enc cf tr x)
        hx⟩

end ClassicalConstraints
