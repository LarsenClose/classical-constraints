/-
  ClassicalConstraints/Chain3_Descriptive/BridgeVacuity.lean
  DescriptiveTransferHypothesis is uninhabitable in TC models.

  The lock theorem (no_poly_sat_solver_descriptive) takes SelfAppUnbounded,
  DescriptiveTransferHypothesis, and a PolyTimeSolver, and derives False.
  This file proves that DescriptiveTransferHypothesis + SelfAppUnbounded
  already gives False — the solver hypothesis is redundant,
  and the lock theorem is vacuously true.

  The proof: bounded selectors always exist (constant functions).
  DescriptiveTransferHypothesis maps any bounded selector to a grade-bounded
  function agreeing with selfApp. Side A says no such function
  exists when selfApp is unbounded. Contradiction.

  STATUS: 0 sorry, 0 Classical.choice.
-/

import ClassicalConstraints.Chain3_Descriptive.DescriptiveComplexityLock

namespace ClassicalConstraints

-- ════════════════════════════════════════════════════════════
-- Section 1: Bounded selectors always exist
-- ════════════════════════════════════════════════════════════

/-- A constant bounded selector exists for any SAT instance at any
    capacity. The input type of DescriptiveTransferHypothesis.transfer is
    always inhabited. -/
def trivialSelector_D3 (φ : SATInstance) (d : Nat) : BoundedSelector φ d where
  select := fun _ => true
  accessed_vars := []
  h_bounded := Nat.zero_le d
  h_factors := fun _ _ _ => rfl

-- ════════════════════════════════════════════════════════════
-- Section 2: DescriptiveTransferHypothesis is uninhabitable
-- ════════════════════════════════════════════════════════════

/-- DescriptiveTransferHypothesis is uninhabitable when SelfAppUnbounded holds.

    Proof: construct a trivial bounded selector at capacity 0,
    apply the transfer to get a grade-0-bounded function agreeing
    with selfApp on grade-0 inputs, contradict Side A.

    The solver hypothesis in no_poly_sat_solver_descriptive is redundant.
    The contradiction comes from DescriptiveTransferHypothesis +
    SelfAppUnbounded alone. -/
theorem descriptive_transfer_hypothesis_uninhabitable
    (M : GradedReflModel_Mirror_D3)
    (hub : SelfAppUnbounded_Mirror_D3 M)
    (family : SATFamily)
    (enc : CookEncoding)
    (df : DefinabilityFaithful enc)
    (tr : DescriptiveTransferHypothesis M family enc df) :
    False := by
  let sel := trivialSelector_D3 (family 0) 0
  obtain ⟨f, hbound, hagree⟩ := tr.transfer 0 0 sel
  exact sideA_bounded_selector_impossible M hub 0
    ⟨f, hagree, fun x _ => hbound x⟩

-- ════════════════════════════════════════════════════════════
-- Section 3: The lock theorem is vacuously true
-- ════════════════════════════════════════════════════════════

/-- The lock theorem's hypothesis set is unsatisfiable.
    No DescriptiveTransferHypothesis can be constructed in any model
    where SelfAppUnbounded holds.

    DescriptiveTransferHypothesis is a Type (structure), not a Prop,
    so we state emptiness as a function to False. -/
theorem descriptive_lock_hypothesis_unsatisfiable
    (M : GradedReflModel_Mirror_D3)
    (hub : SelfAppUnbounded_Mirror_D3 M)
    (family : SATFamily)
    (enc : CookEncoding)
    (df : DefinabilityFaithful enc) :
    DescriptiveTransferHypothesis M family enc df → False :=
  descriptive_transfer_hypothesis_uninhabitable M hub family enc df

/-- The solver hypothesis in no_poly_sat_solver_descriptive is redundant.
    The lock fires from DescriptiveTransferHypothesis + SelfAppUnbounded
    alone, for any solver or no solver. -/
theorem descriptive_solver_hypothesis_redundant
    (M : GradedReflModel_Mirror_D3)
    (hub : SelfAppUnbounded_Mirror_D3 M)
    (family : SATFamily)
    (enc : CookEncoding)
    (df : DefinabilityFaithful enc)
    (tr : DescriptiveTransferHypothesis M family enc df) :
    ∀ _ : PolyTimeSolver family, False :=
  fun _ => descriptive_transfer_hypothesis_uninhabitable M hub family enc df tr

-- ════════════════════════════════════════════════════════════
-- Section 4: DescriptiveTransferHypothesis entails grade-non-increasing
-- ════════════════════════════════════════════════════════════

/-- DescriptiveTransferHypothesis implies selfApp is grade-non-increasing.

    For any x, invoke the transfer at d = grade(x) with a trivial
    selector. The returned function agrees with selfApp at x and
    has grade output ≤ grade(x). Therefore grade(selfApp(x)) ≤ grade(x).

    This is strictly stronger than PEqNP. -/
theorem descriptive_transfer_implies_grade_nonincreasing
    (M : GradedReflModel_Mirror_D3)
    (family : SATFamily)
    (enc : CookEncoding)
    (df : DefinabilityFaithful enc)
    (tr : DescriptiveTransferHypothesis M family enc df) :
    ∀ x, M.grade (M.selfApp x) ≤ M.grade x := by
  intro x
  obtain ⟨f, hbound, hagree⟩ := tr.transfer 0 (M.grade x)
    (trivialSelector_D3 (family 0) (M.grade x))
  rw [← hagree x (Nat.le_refl _)]
  exact hbound x

/-- Alternative proof of uninhabitability via grade-non-increasing. -/
theorem descriptive_transfer_uninhabitable_via_nonincreasing
    (M : GradedReflModel_Mirror_D3)
    (hub : SelfAppUnbounded_Mirror_D3 M)
    (family : SATFamily)
    (enc : CookEncoding)
    (df : DefinabilityFaithful enc)
    (tr : DescriptiveTransferHypothesis M family enc df) :
    False :=
  selfApp_nonincreasing_contradiction M hub M.selfApp
    (fun _ => rfl)
    (descriptive_transfer_implies_grade_nonincreasing M family enc df tr)

-- ════════════════════════════════════════════════════════════
-- Section 5: DescriptiveTransferHypothesis implies PEqNP at every grade
-- ════════════════════════════════════════════════════════════

/-- DescriptiveTransferHypothesis implies selfApp factors through every grade. -/
theorem descriptive_transfer_implies_factors_through_all
    (M : GradedReflModel_Mirror_D3)
    (family : SATFamily)
    (enc : CookEncoding)
    (df : DefinabilityFaithful enc)
    (tr : DescriptiveTransferHypothesis M family enc df) :
    ∀ d, FactorsThrough_Mirror M M.selfApp d := by
  intro d x hx
  have := descriptive_transfer_implies_grade_nonincreasing M family enc df tr x
  omega

/-- DescriptiveTransferHypothesis implies PEqNP. -/
theorem descriptive_transfer_implies_peqnp
    (M : GradedReflModel_Mirror_D3)
    (family : SATFamily)
    (enc : CookEncoding)
    (df : DefinabilityFaithful enc)
    (tr : DescriptiveTransferHypothesis M family enc df) :
    PEqNP_Mirror M :=
  ⟨0, descriptive_transfer_implies_factors_through_all M family enc df tr 0⟩

-- ════════════════════════════════════════════════════════════
-- Section 6: Complete characterization
-- ════════════════════════════════════════════════════════════

/-- What DescriptiveTransferHypothesis actually requires of a model:
    (1) selfApp is grade-non-increasing,
    (2) selfApp factors through every grade,
    (3) PEqNP holds,
    (4) SelfAppUnbounded is impossible.

    The bridge condition is equivalent to a regime assertion.
    The "open condition" is not independent of the regime question —
    it IS the regime question. -/
theorem descriptive_transfer_hypothesis_characterization
    (M : GradedReflModel_Mirror_D3)
    (family : SATFamily)
    (enc : CookEncoding)
    (df : DefinabilityFaithful enc)
    (tr : DescriptiveTransferHypothesis M family enc df) :
    (∀ x, M.grade (M.selfApp x) ≤ M.grade x) ∧
    (∀ d, FactorsThrough_Mirror M M.selfApp d) ∧
    PEqNP_Mirror M ∧
    ¬SelfAppUnbounded_Mirror_D3 M :=
  ⟨descriptive_transfer_implies_grade_nonincreasing M family enc df tr,
   descriptive_transfer_implies_factors_through_all M family enc df tr,
   descriptive_transfer_implies_peqnp M family enc df tr,
   fun hub => descriptive_transfer_hypothesis_uninhabitable M hub family enc df tr⟩

end ClassicalConstraints
