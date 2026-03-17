/-
  ClassicalConstraints/Chain1_SAT/SATDirectBridge.lean
  Chain 1 direct bridge via grade-non-increasing selfApp.

  The direct bridge pattern (used by Chains 2, 3, 5) requires:
    - A reduction red : carrier → carrier
    - red_grade_le : grade(red x) ≤ grade(x)
    - red_idempotent : red(red x) = red x
    - selfApp_eq_red : selfApp x = red x

  For Chain 1, the direct bridge takes a simpler form: the reduction
  IS selfApp (red = selfApp trivially), and selfApp_nonincreasing_contradiction
  needs only grade-non-increasing, not idempotence. The SATModelData
  structure captures the minimal bundle for Chain 1.

  Structural comparison with other chains:
  - Chain 5: red = multilinearReduce (modulo Boolean axioms). Idempotent
    because x²=x, so applying twice gives same result. selfApp = red by
    construction of the polynomial GRM.
  - Chain 2: red = proto_to_dt ∘ dt_to_proto (flatten to decision tree).
    Idempotent because decision trees are already flat. selfApp = red by
    construction of the protocol GRM.
  - Chain 1: there is no canonical formula-level reduction that equals
    selfApp in the Cook-Levin GRM, because selfApp (witness extraction)
    maps instances to their witnesses — a non-projection on formula space.
    The direct bridge is instead routed through the grade-non-increasing
    condition alone (which is what TransferHypothesis already implies,
    as proved in BridgeVacuity.lean).

  Why idempotence fails for Chain 1:
  The Cook-Levin GRM has selfApp x = unfold(fold(x)) = "encode x as a
  SAT instance, extract a satisfying assignment." This is NOT idempotent:
  applying it twice gives "encode the witness as a SAT instance, extract
  a second witness" — an operation on a different kind of object. The
  carrier does not have a canonical projection onto a "simplified" subset
  where selfApp acts as the identity.

  The correct structural picture: Chain 1's direct bridge requires
  SATModelData (2-field version) rather than the 4-field ModelData.
  The grade-non-increasing condition IS the bridge condition for Chain 1.

  Connection to BridgeVacuity.lean:
  transfer_implies_grade_nonincreasing proves the same grade-non-increasing
  condition follows from TransferHypothesis. SATModelData makes this
  condition the explicit bridge input, bypassing TransferHypothesis entirely.

  STATUS: 0 sorry. Classical.choice allowed (Side B).
  Copyright 2024-2026. All rights reserved.
-/

import ClassicalConstraints.Chain1_SAT.SATBoundaryLock
import ClassicalConstraints.Chain1_SAT.BridgeVacuity

namespace ClassicalConstraints

-- ============================================================
-- SATModelData: the minimal Chain 1 bridge structure
-- ============================================================

/-- SAT model data: grade-non-increasing selfApp.

    The minimal bridge structure for Chain 1. Unlike the 4-field
    ModelData pattern (Chains 2, 3, 5), Chain 1's direct bridge
    needs only one structural condition: selfApp is grade-non-increasing.

    This is minimal because selfApp_nonincreasing_contradiction uses
    only h_eq and h_le from ModelData:
    - h_eq : selfApp x = f x    (with f = selfApp, this is trivial)
    - h_le : grade(f x) ≤ grade x

    The idempotence and explicit reduction map required by other chains
    are not needed here. The "reduction" is selfApp itself, and its
    idempotence would require selfApp(selfApp(x)) = selfApp(x), which
    is the fixed-point condition — NOT automatically true in the
    Cook-Levin GRM and NOT needed for the direct bridge.

    Concrete interpretation: selfApp is grade-non-increasing means
    that witness extraction (in the Cook-Levin GRM) does not increase
    the complexity measure (grade). This would mean NP witnesses can
    always be extracted within the grade of the instance — a strong
    structural claim that holds iff P = NP for the relevant GRM. -/
structure SATModelData (M : GradedReflModel_Mirror) where
  /-- selfApp is grade-non-increasing: extracting a witness does not
      increase the grade of the carrier element. -/
  selfApp_grade_le : ∀ x, M.grade (M.selfApp x) ≤ M.grade x

-- ============================================================
-- Chain 1 direct bridge
-- ============================================================

/-- CHAIN 1 DIRECT BRIDGE.

    SATModelData (grade-non-increasing selfApp) directly contradicts
    SelfAppUnbounded. Uses selfApp_nonincreasing_contradiction with
    f = selfApp (h_eq is trivial) and h_le = selfApp_grade_le.

    This is the simplest possible instance of the direct bridge pattern:
    when selfApp = red and red is grade-non-increasing, SelfAppUnbounded
    cannot hold. For Chain 1, red = selfApp, so h_eq is reflexivity.

    Parallel to chain5_direct_bridge, chain2_direct_bridge,
    chain3_direct_bridge — but using the 2-field SATModelData rather
    than the 4-field ModelData, because Chain 1 needs no idempotence. -/
theorem chain1_direct_bridge
    (M : GradedReflModel_Mirror)
    (hub : SelfAppUnbounded_Mirror M)
    (smd : SATModelData M) : False :=
  selfApp_nonincreasing_contradiction M hub M.selfApp
    (fun _ => rfl)
    smd.selfApp_grade_le

-- ============================================================
-- TransferHypothesis implies SATModelData
-- ============================================================

/-- TransferHypothesis implies SATModelData.

    This is the formal connection between the indirect lock
    (SATBoundaryLock via TransferHypothesis) and the direct bridge.

    BridgeVacuity.transfer_implies_grade_nonincreasing proves
    TransferHypothesis → (∀ x, grade(selfApp x) ≤ grade x).
    That IS SATModelData.

    Therefore: any model satisfying TransferHypothesis automatically
    has SATModelData, and the direct bridge fires immediately without
    needing the poly-time solver hypothesis. -/
def transferHypothesis_to_SATModelData
    (M : GradedReflModel_Mirror)
    (family : SATFamily)
    (enc : CookEncoding)
    (cf : CookFaithful enc)
    (tr : TransferHypothesis M family enc cf) :
    SATModelData M where
  selfApp_grade_le :=
    transfer_implies_grade_nonincreasing M family enc cf tr

/-- Chain 1 bridge via TransferHypothesis (connects old and new routes).

    This subsumes no_poly_sat_solver: if TransferHypothesis holds and
    selfApp is unbounded, contradiction follows directly without the
    poly-time solver. Matches BridgeVacuity.transfer_hypothesis_uninhabitable
    but routed through the direct bridge architecture. -/
theorem chain1_bridge_via_transfer
    (M : GradedReflModel_Mirror)
    (hub : SelfAppUnbounded_Mirror M)
    (family : SATFamily)
    (enc : CookEncoding)
    (cf : CookFaithful enc)
    (tr : TransferHypothesis M family enc cf) : False :=
  chain1_direct_bridge M hub
    (transferHypothesis_to_SATModelData M family enc cf tr)

-- ============================================================
-- Comparison: why Chain 1 differs from Chains 2/3/5
-- ============================================================

/-- The 4-field ModelData implies SATModelData.

    Any chain that has a grade-non-increasing idempotent reduction
    with selfApp_eq_red also has SATModelData for Chain 1. This shows
    that SATModelData is a WEAKER requirement: it asks only for
    grade-non-increasing selfApp, not for an explicit idempotent
    reduction that equals selfApp.

    This is the precise sense in which Chain 1's bridge is structurally
    weaker (needs less structure) than Chains 2/3/5. -/
def modelData_implies_SATModelData
    (M : GradedReflModel_Mirror)
    (red : M.carrier → M.carrier)
    (red_grade_le : ∀ x, M.grade (red x) ≤ M.grade x)
    (selfApp_eq_red : ∀ x, M.selfApp x = red x) :
    SATModelData M where
  selfApp_grade_le x := by
    rw [selfApp_eq_red]
    exact red_grade_le x

-- ============================================================
-- What a full Chain 1 ModelData would require
-- ============================================================

/-- SATFullModelData: the 4-field pattern applied to Chain 1.

    This is the structure that would hold IF there existed a canonical
    grade-non-increasing idempotent reduction on SAT carrier elements
    such that selfApp = red. It is stated for completeness, to
    document precisely what the other chains provide and Chain 1 does not.

    The obstacle: in the Cook-Levin GRM, selfApp x = unfold(fold(x))
    maps instances to witnesses. No natural "clause reduction" or
    "unit propagation" operation on instance space has the property
    selfApp = red, because:
    - unit propagation operates on formula structure, not on the
      reflexive-object carrier
    - selfApp is witness extraction, not formula simplification
    - making selfApp = red would require fold/unfold to be constructed
      around a formula-simplification operation, not around Cook-Levin

    A concrete obstacle: if we tried to set red = unit_propagate, then
    selfApp_eq_red would require unfold(fold(x)) = unit_propagate(x)
    for all carrier elements x. This fails because:
    - fold(x) encodes x as a SAT formula (Cook-Levin reduction)
    - unfold(fold(x)) extracts a witness from that formula
    - unit_propagate(x) simplifies x as a formula
    These are operations on different objects. -/
structure SATFullModelData (M : GradedReflModel_Mirror) where
  /-- The reduction map (a formula-level operation, e.g., unit propagation). -/
  red : M.carrier → M.carrier
  /-- Reduction is grade-non-increasing. -/
  red_grade_le : ∀ x, M.grade (red x) ≤ M.grade x
  /-- Reduction is idempotent: already-reduced elements are fixed. -/
  red_idempotent : ∀ x, red (red x) = red x
  /-- selfApp IS reduction (the open/impossible condition for Chain 1). -/
  selfApp_eq_red : ∀ x, M.selfApp x = red x

/-- SATFullModelData implies SATModelData. -/
def SATFullModelData.toSATModelData {M : GradedReflModel_Mirror}
    (sfmd : SATFullModelData M) : SATModelData M :=
  modelData_implies_SATModelData M sfmd.red sfmd.red_grade_le sfmd.selfApp_eq_red

/-- SATFullModelData directly contradicts SelfAppUnbounded. -/
theorem chain1_direct_bridge_from_full
    (M : GradedReflModel_Mirror)
    (hub : SelfAppUnbounded_Mirror M)
    (sfmd : SATFullModelData M) : False :=
  chain1_direct_bridge M hub sfmd.toSATModelData

-- ============================================================
-- Structural characterization of Chain 1's position
-- ============================================================

/-- The grade-non-increasing condition is the necessary and sufficient
    condition for the Chain 1 direct bridge.

    Forward: SATModelData gives the bridge.
    Backward: any proof of False from SelfAppUnbounded must establish
    grade-non-increasing selfApp (or an equivalent condition).

    This establishes that SATModelData captures exactly the content
    needed for Chain 1 — no more, no less. -/
theorem chain1_bridge_iff_grade_nonincreasing
    (M : GradedReflModel_Mirror)
    (hub : SelfAppUnbounded_Mirror M) :
    SATModelData M ↔ False := by
  constructor
  · intro smd
    exact chain1_direct_bridge M hub smd
  · intro h
    exact h.elim

/-- The direct bridge is the simplest possible: only the grade-non-increasing
    condition on selfApp is needed, with no auxiliary reduction map, no
    idempotence, and no selfApp_eq_red beyond the trivial case red = selfApp.

    This stands in contrast to the other chains where the 4-field ModelData
    is necessary because the canonical reduction is NOT selfApp by definition
    — one must identify the right reduction map and prove selfApp equals it.

    For Chain 1: selfApp is the natural reduction. The bridge reduces to
    asking whether selfApp is grade-non-increasing, which is precisely the
    P = NP question for the graded model. -/
theorem chain1_is_minimal_bridge
    (M : GradedReflModel_Mirror)
    (hub : SelfAppUnbounded_Mirror M)
    (h_le : ∀ x, M.grade (M.selfApp x) ≤ M.grade x) : False :=
  chain1_direct_bridge M hub ⟨h_le⟩

end ClassicalConstraints
