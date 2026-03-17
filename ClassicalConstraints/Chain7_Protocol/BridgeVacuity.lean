/-
  ClassicalConstraints/Chain7_Protocol/BridgeVacuity.lean
  ProtocolTransfer is uninhabitable in TC models.

  The lock theorem (no_bounded_protocol_shortcuts) takes SelfAppUnbounded,
  ProtocolTransfer, and a PolyTimeSolver, and derives False.
  This file proves that ProtocolTransfer + SelfAppUnbounded
  already gives False — the solver hypothesis is redundant,
  and the lock theorem is vacuously true.

  The proof: bounded selectors always exist (constant functions).
  ProtocolTransfer maps any bounded selector to a grade-bounded
  function agreeing with selfApp. Side A says no such function
  exists when selfApp is unbounded. Contradiction.

  STATUS: 0 sorry, 0 Classical.choice.
-/

import ClassicalConstraints.Chain7_Protocol.ProtocolWitnessFamilyLock

namespace ClassicalConstraints

-- ════════════════════════════════════════════════════════════
-- Section 1: Bounded selectors always exist
-- ════════════════════════════════════════════════════════════

/-- A constant bounded selector exists for any SAT instance at any
    capacity. The input type of ProtocolTransfer.transfer is
    always inhabited. -/
def trivialSelector_protocol (φ : SATInstance) (d : Nat) : BoundedSelector φ d where
  select := fun _ => true
  accessed_vars := []
  h_bounded := Nat.zero_le d
  h_factors := fun _ _ _ => rfl

-- ════════════════════════════════════════════════════════════
-- Section 2: ProtocolTransfer is uninhabitable in TC models
-- ════════════════════════════════════════════════════════════

/-- ProtocolTransfer is uninhabitable when SelfAppUnbounded holds.

    Proof: construct a trivial bounded selector at capacity 0,
    apply the transfer to get a grade-0-bounded function agreeing
    with selfApp on grade-0 inputs, contradict Side A.

    The solver hypothesis in no_bounded_protocol_shortcuts is redundant.
    The contradiction comes from ProtocolTransfer +
    SelfAppUnbounded alone. -/
theorem protocol_transfer_uninhabitable
    (M : GradedReflModel_Mirror)
    (hub : SelfAppUnbounded_Mirror M)
    (family : SATFamily)
    (enc : CookEncoding)
    (cf : ConsequenceFaithful enc)
    (tr : ProtocolTransfer M family enc cf) :
    False := by
  let sel := trivialSelector_protocol (family 0) 0
  obtain ⟨f, hbound, hagree⟩ := tr.transfer 0 0 sel
  exact sideA_bounded_selector_impossible M hub 0
    ⟨f, hagree, fun x _ => hbound x⟩

-- ════════════════════════════════════════════════════════════
-- Section 3: The lock theorem is vacuously true
-- ════════════════════════════════════════════════════════════

/-- The lock theorem's hypothesis set is unsatisfiable.
    No ProtocolTransfer can be constructed in any model
    where SelfAppUnbounded holds.

    ProtocolTransfer is a Type (structure), not a Prop,
    so we state emptiness as a function to False. -/
theorem protocol_lock_hypothesis_unsatisfiable
    (M : GradedReflModel_Mirror)
    (hub : SelfAppUnbounded_Mirror M)
    (family : SATFamily)
    (enc : CookEncoding)
    (cf : ConsequenceFaithful enc) :
    ProtocolTransfer M family enc cf → False :=
  protocol_transfer_uninhabitable M hub family enc cf

/-- The solver hypothesis in no_bounded_protocol_shortcuts is redundant.
    The lock fires from ProtocolTransfer + SelfAppUnbounded
    alone, for any solver or no solver. -/
theorem protocol_solver_hypothesis_redundant
    (M : GradedReflModel_Mirror)
    (hub : SelfAppUnbounded_Mirror M)
    (family : SATFamily)
    (enc : CookEncoding)
    (cf : ConsequenceFaithful enc)
    (tr : ProtocolTransfer M family enc cf) :
    ∀ _ : PolyTimeSolver family, False :=
  fun _ => protocol_transfer_uninhabitable M hub family enc cf tr

-- ════════════════════════════════════════════════════════════
-- Section 4: ProtocolTransfer implies grade-non-increasing
-- ════════════════════════════════════════════════════════════

/-- ProtocolTransfer implies selfApp is grade-non-increasing.

    For any x, invoke the transfer at d = grade(x) with a trivial
    selector. The returned function agrees with selfApp at x and
    has grade output ≤ grade(x). Therefore grade(selfApp(x)) ≤ grade(x).

    This is strictly stronger than PEqNP. -/
theorem protocol_transfer_implies_grade_nonincreasing
    (M : GradedReflModel_Mirror)
    (family : SATFamily)
    (enc : CookEncoding)
    (cf : ConsequenceFaithful enc)
    (tr : ProtocolTransfer M family enc cf) :
    ∀ x, M.grade (M.selfApp x) ≤ M.grade x := by
  intro x
  obtain ⟨f, hbound, hagree⟩ := tr.transfer 0 (M.grade x)
    (trivialSelector_protocol (family 0) (M.grade x))
  rw [← hagree x (Nat.le_refl _)]
  exact hbound x

/-- Alternative proof of uninhabitability via grade-non-increasing. -/
theorem protocol_transfer_uninhabitable_via_nonincreasing
    (M : GradedReflModel_Mirror)
    (hub : SelfAppUnbounded_Mirror M)
    (family : SATFamily)
    (enc : CookEncoding)
    (cf : ConsequenceFaithful enc)
    (tr : ProtocolTransfer M family enc cf) :
    False :=
  selfApp_nonincreasing_contradiction M hub M.selfApp
    (fun _ => rfl)
    (protocol_transfer_implies_grade_nonincreasing M family enc cf tr)

-- ════════════════════════════════════════════════════════════
-- Section 5: ProtocolTransfer implies PEqNP at every grade
-- ════════════════════════════════════════════════════════════

/-- ProtocolTransfer implies selfApp factors through every grade.
    Grade-non-increasing entails FactorsThrough at every d. -/
theorem protocol_transfer_implies_factors_through_all
    (M : GradedReflModel_Mirror)
    (family : SATFamily)
    (enc : CookEncoding)
    (cf : ConsequenceFaithful enc)
    (tr : ProtocolTransfer M family enc cf) :
    ∀ d, FactorsThrough_Mirror M M.selfApp d := by
  intro d x hx
  have := protocol_transfer_implies_grade_nonincreasing M family enc cf tr x
  omega

/-- ProtocolTransfer implies PEqNP. -/
theorem protocol_transfer_implies_peqnp
    (M : GradedReflModel_Mirror)
    (family : SATFamily)
    (enc : CookEncoding)
    (cf : ConsequenceFaithful enc)
    (tr : ProtocolTransfer M family enc cf) :
    PEqNP_Mirror M :=
  ⟨0, protocol_transfer_implies_factors_through_all M family enc cf tr 0⟩

-- ════════════════════════════════════════════════════════════
-- Section 6: Complete characterization
-- ════════════════════════════════════════════════════════════

/-- What ProtocolTransfer actually requires of a model:
    (1) selfApp is grade-non-increasing,
    (2) selfApp factors through every grade,
    (3) PEqNP holds,
    (4) SelfAppUnbounded is impossible.

    The bridge condition is equivalent to a regime assertion.
    The "open condition" is not independent of the regime question —
    it IS the regime question. -/
theorem protocol_transfer_characterization
    (M : GradedReflModel_Mirror)
    (family : SATFamily)
    (enc : CookEncoding)
    (cf : ConsequenceFaithful enc)
    (tr : ProtocolTransfer M family enc cf) :
    (∀ x, M.grade (M.selfApp x) ≤ M.grade x) ∧
    (∀ d, FactorsThrough_Mirror M M.selfApp d) ∧
    PEqNP_Mirror M ∧
    ¬SelfAppUnbounded_Mirror M :=
  ⟨protocol_transfer_implies_grade_nonincreasing M family enc cf tr,
   protocol_transfer_implies_factors_through_all M family enc cf tr,
   protocol_transfer_implies_peqnp M family enc cf tr,
   fun hub => protocol_transfer_uninhabitable M hub family enc cf tr⟩

/-! ## Summary

This file proves six results for Chain 7 (Protocol):

1. **trivialSelector_protocol**: Bounded selectors always exist (constant functions).
   The input type of ProtocolTransfer.transfer is always inhabited.

2. **protocol_transfer_uninhabitable**: ProtocolTransfer + SelfAppUnbounded → False.
   The lock theorem's hypotheses are jointly inconsistent.

3. **protocol_lock_hypothesis_unsatisfiable / protocol_solver_hypothesis_redundant**:
   The solver in no_bounded_protocol_shortcuts contributes nothing.
   The contradiction comes from the other hypotheses alone.

4. **protocol_transfer_implies_grade_nonincreasing**: ProtocolTransfer forces
   selfApp to be grade-non-increasing. This is strictly stronger than PEqNP.

5. **protocol_transfer_implies_factors_through_all / protocol_transfer_implies_peqnp**:
   ProtocolTransfer implies PEqNP (and factoring at every grade).

6. **protocol_transfer_characterization**: ProtocolTransfer is
   equivalent to a regime assertion. The bridge condition IS the
   regime question. There is no independent "bridge gap."
-/

end ClassicalConstraints
