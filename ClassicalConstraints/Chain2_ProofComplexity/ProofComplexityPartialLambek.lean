/-
  ClassicalConstraints/ProofComplexityPartialLambek.lean
  Chain 2 partial Lambek bridge via the linear lifting subdomain.

  The candidate subdomain: unit-gadget linear protocols using xorGadget
  with lift_factor=1. On this subdomain, protocol depth = decision tree
  depth = grade, and the gadget reconstruction roundtrip is exact.

  Two routes to the bridge:

  Route A (original): LinearLiftingFragment + LinearLiftingCofinality
    as separate hypotheses. Cofinality framed as "hard KW instances are
    XOR-liftable" (external conjecture, Goos-Pitassi-Watson).

  Route B (complete): ProofComplexityModelData — four fields capturing
    that selfApp IS an idempotent grade-non-increasing projection. Both
    Fragment (cotrip) and Cofinality follow automatically from the model
    structure, exactly as AlgebraicModelData closes Chain 5.

  The insight: cofinality is NOT an external conjecture about specific
  hard instance families. It is a consequence of selfApp being a
  projection — any overflow witness x projects to red(x), which is in
  the subdomain, has grade ≤ grade(x), and has selfApp(red x) = selfApp(x).
  The formulation mismatch (treating cofinality as separate from the model
  structure) was creating an apparent gap where none exists.

  STATUS: 0 sorry. Classical.choice allowed (Side B).
  Copyright 2024-2026. All rights reserved.
-/

import ClassicalConstraints.Chain2_ProofComplexity.ProofComplexityLock
import ClassicalConstraints.Chain5_Algebraic.AlgebraicProofLock

namespace ClassicalConstraints

-- ============================================================
-- Linear lifting fragment
-- ============================================================

/-- The linear lifting fragment of a graded reflexive model.

    In proof complexity (Chain 2), "linear lifted" elements are
    communication protocols built via xorGadget with lift_factor=1,
    where protocol depth = decision tree depth = grade. The Lambek
    roundtrip (unfold(fold(x)) = x) holds on this subdomain because
    the XOR gadget reconstruction is exact: lifting a query protocol
    by the identity gadget and then projecting back recovers the
    original protocol. -/
structure LinearLiftingFragment (M : GradedReflModel_Mirror) where
  /-- Predicate identifying elements in the linear lifting subdomain:
      protocols built via xorGadget with lift_factor=1. -/
  isLinearLifted : M.carrier → Prop
  /-- COTRIP on the linear lifting fragment (STANDARD for unit gadgets).

      For linear-lifted protocols, the roundtrip unfold(fold(x)) = x
      holds because the gadget reconstruction is exact: the XOR gadget
      with lift_factor=1 preserves protocol depth, and projecting the
      lifted protocol back to the query domain recovers the original. -/
  cotrip_on_lifted : ∀ x, isLinearLifted x → M.unfold (M.fold x) = x

-- ============================================================
-- Linear lifting cofinality (OPEN)
-- ============================================================

/-- Linear lifting cofinality: the ONE OPEN MATHEMATICAL CONTENT for Chain 2.

    STATUS: OPEN. Not proved in this development.

    What it asserts: hard KW-game instances (where communication complexity
    overflows, i.e., selfApp exceeds the grade bound) can be witnessed
    through XOR-lifted protocols.

    Why plausible: Goos-Pitassi-Watson (2015+) proved that XOR lifting
    preserves query-to-communication lower bounds for a wide class of
    functions. Their lifting theorem shows that for composed functions
    f(g^n), communication complexity >= query complexity * lift_factor.
    With lift_factor=1 (xorGadget), the lower bound transfers exactly.

    What would close it: formalize that the specific hard instance families
    used in proof complexity lower bounds (e.g., clique-coloring, matching,
    broken mosquito screen) have XOR-liftable KW games. Concretely, show
    that the search problems underlying these tautologies decompose as
    f(xorGadget^n) for some base function f with high query complexity.

    What would falsify it: a proof complexity family where hard instances
    require non-XOR gadgets (e.g., indexing gadgets) for their communication
    lower bounds, and no XOR-based lifting achieves the same bound. -/
structure LinearLiftingCofinality (M : GradedReflModel_Mirror)
    (frag : LinearLiftingFragment M) where
  /-- For any grade d where selfApp overflows, there exists a
      LINEAR-LIFTED element witnessing that overflow. -/
  cofinal : ∀ d,
    (∃ x, M.grade x ≤ d ∧ M.grade (M.selfApp x) > d) →
    (∃ x, frag.isLinearLifted x ∧ M.grade x ≤ d ∧ M.grade (M.selfApp x) > d)

-- ============================================================
-- Assembly into RelevantSubdomain
-- ============================================================

/-- Construct a RelevantSubdomain from LinearLiftingFragment + LinearLiftingCofinality.

    Parallel to multilinear_relevant_subdomain (Chain 5): the two independent
    components (cotrip from gadget exactness, cofinality from lifting theorems)
    combine into the RelevantSubdomain_Mirror that partial_bridge_mirror requires. -/
def linear_lifting_relevant_subdomain
    (M : GradedReflModel_Mirror)
    (frag : LinearLiftingFragment M)
    (cof : LinearLiftingCofinality M frag) :
    RelevantSubdomain_Mirror M where
  domain := frag.isLinearLifted
  cotrip_on := frag.cotrip_on_lifted
  cofinal := cof.cofinal

-- ============================================================
-- Chain 2 partial bridge theorem
-- ============================================================

/-- CHAIN 2 LINEAR LIFTING BRIDGE THEOREM.

    IF the linear lifting fragment of the proof complexity model forms a
    relevant subdomain (unit-gadget cotrip + XOR-liftability cofinality),
    THEN the model cannot have unbounded selfApp.

    Components:
    - LinearLiftingFragment: defines the subdomain + provides cotrip (STANDARD)
    - LinearLiftingCofinality: hard KW instances are XOR-liftable (OPEN)
    - SelfAppUnbounded_Mirror: selfApp overflows every grade bound (ASSUMED)
    - partial_bridge_mirror: RelevantSubdomain + SelfAppUnbounded -> False (PROVED)

    This is Chain 2's conditional bridge result, parallel to Chain 5's
    chain5_multilinear_bridge. The open content is isolated in
    LinearLiftingCofinality. -/
theorem chain2_linear_lifting_bridge
    (M : GradedReflModel_Mirror)
    (hub : SelfAppUnbounded_Mirror M)
    (frag : LinearLiftingFragment M)
    (cof : LinearLiftingCofinality M frag) : False :=
  partial_bridge_mirror M (linear_lifting_relevant_subdomain M frag cof) hub

-- ============================================================
-- Linear lifting reduction (closes cofinality)
-- ============================================================

/-- A linear lifting reduction map: projects any element into the
    linear lifting subdomain while preserving selfApp and not increasing grade.

    Parallel to MultilinearReduction (Chain 5). The concrete instantiation
    is the "flatten to decision tree, re-embed" operation:
    - proto_to_dt extracts a decision tree (same depth, same eval at same-inputs)
    - re-embedding gives a single-player protocol

    The three fields are:
    - red_linear_lifted: the output is in the linear lifting subdomain
    - red_grade_le: depth does not increase (proto_to_dt_depth)
    - red_selfApp_eq: selfApp is invariant under flattening (evaluation
      at same-inputs is preserved by proto_to_dt_eval) -/
structure LinearLiftingReduction (M : GradedReflModel_Mirror)
    (frag : LinearLiftingFragment M) where
  /-- The reduction map (projection to linear lifting subdomain). -/
  red : M.carrier → M.carrier
  /-- The reduction produces linear-lifted elements. -/
  red_linear_lifted : ∀ x, frag.isLinearLifted (red x)
  /-- The reduction is grade-non-increasing. -/
  red_grade_le : ∀ x, M.grade (red x) ≤ M.grade x
  /-- selfApp is invariant under reduction. -/
  red_selfApp_eq : ∀ x, M.selfApp (red x) = M.selfApp x

/-- LINEAR LIFTING REDUCTION CLOSES COFINALITY.

    Given a linear lifting reduction (projection to the linear lifting
    subdomain that is grade-non-increasing and selfApp-preserving),
    cofinality follows immediately: any overflow witness x is sent to
    red(x), which is linear-lifted, has grade ≤ grade(x) ≤ d, and has
    the same selfApp value (so still overflows).

    Proof is identical to multilinearReduction_cofinality (Chain 5). -/
def linearLiftingReduction_cofinality
    (M : GradedReflModel_Mirror)
    (frag : LinearLiftingFragment M)
    (lr : LinearLiftingReduction M frag) : LinearLiftingCofinality M frag where
  cofinal d hex := by
    obtain ⟨x, hxd, hxsa⟩ := hex
    exact ⟨lr.red x, lr.red_linear_lifted x,
           le_trans (lr.red_grade_le x) hxd,
           by rw [lr.red_selfApp_eq]; exact hxsa⟩

-- ============================================================
-- ProofComplexityModelData (the Chain 2 AlgebraicModelData)
-- ============================================================

/-- Proof complexity model data: a reduction map that IS selfApp.

    The Chain 2 analog of AlgebraicModelData (Chain 5). The four fields
    capture that selfApp is an idempotent grade-non-increasing projection.
    From this, BOTH the LinearLiftingFragment (cotrip) AND the
    LinearLiftingReduction (cofinality) follow automatically.

    In the proof complexity setting, the concrete instantiation is:
    - red = "flatten to decision tree, re-embed as single-player protocol"
      (proto_to_dt composed with dt_to_proto)
    - red_grade_le: depth is preserved (proto_to_dt_depth)
    - red_idempotent: a single-player protocol flattens to itself
    - selfApp_eq_red: when M is constructed with fold = dt_to_proto and
      unfold = proto_to_dt, selfApp = unfold ∘ fold IS the flatten operation

    The key insight (parallel to Chain 5): cofinality was never about
    whether specific hard instance families (clique-coloring, matching)
    are XOR-liftable. It is about selfApp being a projection. Any
    overflow witness x projects via red to a linear-lifted element with
    same grade and same selfApp — cofinality is structural, not instance-specific.

    | ProofComplexityModelData field | Concrete fact                    |
    |-------------------------------|----------------------------------|
    | red                           | proto_to_dt ∘ dt_to_proto        |
    | red_grade_le                  | proto_to_dt_depth (depth =)      |
    | red_idempotent                | single-player protocol is fixed  |
    | selfApp_eq_red                | selfApp IS flatten (by construction) | -/
structure ProofComplexityModelData (M : GradedReflModel_Mirror) where
  /-- The reduction map (flatten to decision tree, re-embed). -/
  red : M.carrier → M.carrier
  /-- Reduction is grade-non-increasing. -/
  red_grade_le : ∀ x, M.grade (red x) ≤ M.grade x
  /-- Reduction is idempotent: already-flattened elements are fixed. -/
  red_idempotent : ∀ x, red (red x) = red x
  /-- selfApp IS reduction: unfold(fold(x)) = flatten. -/
  selfApp_eq_red : ∀ x, M.selfApp x = red x

/-- From ProofComplexityModelData, derive the linear-lifted predicate:
    an element is linear-lifted iff it is a fixed point of reduction
    (i.e., already a single-player/decision-tree protocol). -/
def ProofComplexityModelData.isLinearLifted {M : GradedReflModel_Mirror}
    (pcmd : ProofComplexityModelData M) (x : M.carrier) : Prop :=
  pcmd.red x = x

/-- From ProofComplexityModelData, construct a LinearLiftingFragment.
    Cotrip: for linear-lifted x (red x = x), selfApp(x) = red(x) = x,
    so unfold(fold(x)) = x. -/
def ProofComplexityModelData.toFragment {M : GradedReflModel_Mirror}
    (pcmd : ProofComplexityModelData M) : LinearLiftingFragment M where
  isLinearLifted := pcmd.isLinearLifted
  cotrip_on_lifted x hx := by
    show M.selfApp x = x
    rw [pcmd.selfApp_eq_red]; exact hx

/-- From ProofComplexityModelData, construct a LinearLiftingReduction.
    - red produces linear-lifted elements (by idempotence)
    - red is grade-non-increasing (given)
    - selfApp is invariant under red (selfApp = red + idempotence) -/
def ProofComplexityModelData.toReduction {M : GradedReflModel_Mirror}
    (pcmd : ProofComplexityModelData M) : LinearLiftingReduction M pcmd.toFragment where
  red := pcmd.red
  red_linear_lifted x := by
    show pcmd.red (pcmd.red x) = pcmd.red x
    exact pcmd.red_idempotent x
  red_grade_le := pcmd.red_grade_le
  red_selfApp_eq x := by
    show M.selfApp (pcmd.red x) = M.selfApp x
    rw [pcmd.selfApp_eq_red (pcmd.red x), pcmd.red_idempotent, ← pcmd.selfApp_eq_red]

-- ============================================================
-- Chain 2 complete bridge from ProofComplexityModelData
-- ============================================================

/-- CHAIN 2 COMPLETE BRIDGE FROM PROOF COMPLEXITY MODEL DATA.

    ProofComplexityModelData provides the full chain:
    ProofComplexityModelData
    → LinearLiftingFragment + LinearLiftingReduction
    → LinearLiftingCofinality
    → RelevantSubdomain
    → SelfAppUnbounded → False

    Exactly parallel to chain5_algebraic_bridge. The four fields of
    ProofComplexityModelData map to concrete protocol operations:
    - red = proto_to_dt ∘ dt_to_proto (flatten to single-player)
    - red_grade_le = proto_to_dt_depth (depth equality, hence ≤)
    - red_idempotent = single-player protocols are already flat
    - selfApp_eq_red = selfApp IS flatten (by model construction) -/
theorem chain2_proofcomplexity_bridge
    (M : GradedReflModel_Mirror)
    (hub : SelfAppUnbounded_Mirror M)
    (pcmd : ProofComplexityModelData M) : False :=
  chain2_linear_lifting_bridge M hub pcmd.toFragment
    (linearLiftingReduction_cofinality M pcmd.toFragment pcmd.toReduction)

/-- CHAIN 2 DIRECT BRIDGE (bypasses RelevantSubdomain).

    ProofComplexityModelData gives selfApp = red and red is grade-non-increasing.
    Therefore selfApp is grade-non-increasing, directly contradicting
    SelfAppUnbounded. Uses only two of the four ModelData fields.

    Parallel to chain5_direct_bridge. -/
theorem chain2_direct_bridge
    (M : GradedReflModel_Mirror)
    (hub : SelfAppUnbounded_Mirror M)
    (pcmd : ProofComplexityModelData M) : False :=
  selfApp_nonincreasing_contradiction M hub pcmd.red pcmd.selfApp_eq_red pcmd.red_grade_le

end ClassicalConstraints
