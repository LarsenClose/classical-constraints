/-
  ClassicalConstraints/DescriptiveComplexityPartialLambek.lean
  Chain 3 partial Lambek bridge via the definability-canonical subdomain.

  The candidate subdomain: FO formulas in canonical form (e.g., negation
  normal form), where quantifier rank = grade. On this subdomain, the
  canonicalization roundtrip is the identity (selfApp(x) = x).

  Two routes to the bridge:

  Route A (original): DefinabilityFragment + DefinabilityCofinality
    as separate hypotheses. Cofinality framed as "hard instances have
    definability-canonical witnesses" (external conjecture about specific
    hard families).

  Route B (complete): DescriptiveComplexityModelData — four fields capturing
    that selfApp IS an idempotent grade-non-increasing projection. Both
    Fragment (cotrip) and Cofinality follow automatically from the model
    structure, exactly as AlgebraicModelData (Chain 5) and
    ProofComplexityModelData (Chain 2) close their respective chains.

  The insight (parallel to Chains 5 and 2): the "four incomparable measures"
  (quantifier rank, pebble count, Gaifman locality, LFP iteration depth)
  are commuting views of the same underlying resource — quantifier rank.
  Gaifman locality derives from quantifier rank; pebble count = variable
  width (Ehrenfeucht-Fraisse); LFP connects to quantifier rank on ordered
  structures (Immerman-Vardi). When the model is properly specified with
  quantifier rank as grade and canonicalization as selfApp, cofinality is
  structural: any overflow witness canonicalizes to an element in the
  subdomain with the same grade and same selfApp.

  STATUS: 0 sorry. Classical.choice allowed (Side B).
  Copyright 2024-2026. All rights reserved.
-/

import ClassicalConstraints.Chain3_Descriptive.DescriptiveComplexityLock
import ClassicalConstraints.Chain5_Algebraic.AlgebraicProofLock

namespace ClassicalConstraints

-- ============================================================
-- Definability-canonical fragment
-- ============================================================

/-- The definability-canonical fragment of a graded reflexive model.

    In descriptive complexity (Chain 3), "definability-canonical" elements
    are FO formulas in canonical form (e.g., negation normal form or
    Hintikka type representatives), where:
    - carrier = FO formulas over SAT vocabulary
    - grade = quantifier rank (the primary resource; all other measures
      — Gaifman locality, pebble count, LFP depth — derive from or
      connect to quantifier rank)
    - fold = extract the model class / Boolean function on structures
    - unfold = express model class as canonical formula
    - selfApp = unfold ∘ fold = canonicalize

    An element x is "definability-canonical" if it is a fixed point of
    canonicalization: selfApp(x) = x. These are formulas already in
    canonical form, where evaluating semantics and re-expressing produces
    the same formula.

    This structure captures that a model has an identifiable subdomain
    where the Lambek cotrip (unfold ∘ fold = id) holds. -/
structure DefinabilityFragment (M : GradedReflModel_Mirror) where
  /-- Predicate identifying definability-canonical elements. -/
  isDefinabilityCanonical : M.carrier → Prop
  /-- COTRIP on the definability-canonical fragment.

      For canonical-form formulas, the roundtrip unfold(fold(x)) = x
      holds because canonicalization is the identity on already-canonical
      formulas. The evaluation-then-reexpression cycle produces the
      same formula when the formula is already in canonical form. -/
  cotrip_on_canonical : ∀ x, isDefinabilityCanonical x → M.unfold (M.fold x) = x

-- ============================================================
-- Definability cofinality (OPEN in Route A)
-- ============================================================

/-- Definability cofinality: the ONE OPEN MATHEMATICAL CONTENT for Chain 3
    under Route A.

    STATUS: OPEN under Route A. CLOSED by Route B (DescriptiveComplexityModelData).

    What it asserts: hard instances (where selfApp overflows the grade
    bound) can be witnessed by definability-canonical elements.

    The "four incomparable measures" framing obscured this: the question
    was cast as whether hard instances require unbounded quantifier rank
    AND unbounded pebble count AND unbounded locality radius AND unbounded
    LFP depth — four separate conditions. But these four measures are
    commuting views of quantifier rank:
    - Gaifman locality radius is bounded by quantifier rank (Gaifman's theorem)
    - Pebble count = variable width (Ehrenfeucht-Fraisse theorem)
    - LFP iteration depth connects to quantifier rank on ordered structures
      (Immerman-Vardi theorem)

    Once the "four measures" are recognized as one, cofinality reduces to:
    any overflow witness canonicalizes to an element in the fragment with
    the same grade and the same selfApp value. This is the same structural
    argument that closed Chains 5 and 2. -/
structure DefinabilityCofinality (M : GradedReflModel_Mirror)
    (frag : DefinabilityFragment M) where
  /-- For any grade d where selfApp overflows, there exists a
      DEFINABILITY-CANONICAL element witnessing that overflow. -/
  cofinal : ∀ d,
    (∃ x, M.grade x ≤ d ∧ M.grade (M.selfApp x) > d) →
    (∃ x, frag.isDefinabilityCanonical x ∧ M.grade x ≤ d ∧ M.grade (M.selfApp x) > d)

-- ============================================================
-- Assembly into RelevantSubdomain
-- ============================================================

/-- Construct a RelevantSubdomain from DefinabilityFragment + DefinabilityCofinality.

    Parallel to multilinear_relevant_subdomain (Chain 5) and
    linear_lifting_relevant_subdomain (Chain 2): the two independent
    components (cotrip from canonicality, cofinality from model structure)
    combine into the RelevantSubdomain_Mirror that partial_bridge_mirror
    requires. -/
def definability_relevant_subdomain
    (M : GradedReflModel_Mirror)
    (frag : DefinabilityFragment M)
    (cof : DefinabilityCofinality M frag) :
    RelevantSubdomain_Mirror M where
  domain := frag.isDefinabilityCanonical
  cotrip_on := frag.cotrip_on_canonical
  cofinal := cof.cofinal

-- ============================================================
-- Chain 3 partial bridge theorem
-- ============================================================

/-- CHAIN 3 DEFINABILITY BRIDGE THEOREM.

    IF the definability-canonical fragment of the descriptive complexity
    model forms a relevant subdomain (canonical-form cotrip + cofinality),
    THEN the model cannot have unbounded selfApp.

    Components:
    - DefinabilityFragment: defines the subdomain + provides cotrip (STANDARD)
    - DefinabilityCofinality: hard instances have canonical witnesses (OPEN in Route A)
    - SelfAppUnbounded_Mirror: selfApp overflows every grade bound (ASSUMED)
    - partial_bridge_mirror: RelevantSubdomain + SelfAppUnbounded -> False (PROVED)

    This is Chain 3's conditional bridge result, parallel to Chain 5's
    chain5_multilinear_bridge and Chain 2's chain2_linear_lifting_bridge. -/
theorem chain3_definability_bridge
    (M : GradedReflModel_Mirror)
    (hub : SelfAppUnbounded_Mirror M)
    (frag : DefinabilityFragment M)
    (cof : DefinabilityCofinality M frag) : False :=
  partial_bridge_mirror M (definability_relevant_subdomain M frag cof) hub

-- ============================================================
-- Definability reduction (closes cofinality)
-- ============================================================

/-- A definability reduction map: projects any element into the
    definability-canonical subdomain while preserving selfApp and not
    increasing grade.

    Parallel to MultilinearReduction (Chain 5) and LinearLiftingReduction
    (Chain 2). The concrete instantiation is formula canonicalization:
    - NNF conversion: push negations to atoms, eliminate double negation
    - Output is in canonical form (definability-canonical)
    - Quantifier depth is preserved (grade-non-increasing)
    - Evaluation is preserved (selfApp-invariant)

    The three fields are:
    - red_canonical: the output is in the definability-canonical subdomain
    - red_grade_le: quantifier depth does not increase
    - red_selfApp_eq: selfApp is invariant under canonicalization -/
structure DefinabilityReduction (M : GradedReflModel_Mirror)
    (frag : DefinabilityFragment M) where
  /-- The reduction map (projection to definability-canonical subdomain). -/
  red : M.carrier → M.carrier
  /-- The reduction produces definability-canonical elements. -/
  red_canonical : ∀ x, frag.isDefinabilityCanonical (red x)
  /-- The reduction is grade-non-increasing. -/
  red_grade_le : ∀ x, M.grade (red x) ≤ M.grade x
  /-- selfApp is invariant under reduction. -/
  red_selfApp_eq : ∀ x, M.selfApp (red x) = M.selfApp x

/-- DEFINABILITY REDUCTION CLOSES COFINALITY.

    Given a definability reduction (projection to the canonical subdomain
    that is grade-non-increasing and selfApp-preserving), cofinality
    follows immediately: any overflow witness x is sent to red(x), which
    is canonical, has grade ≤ grade(x) ≤ d, and has the same selfApp
    value (so still overflows).

    Proof is identical to multilinearReduction_cofinality (Chain 5) and
    linearLiftingReduction_cofinality (Chain 2). -/
def definabilityReduction_cofinality
    (M : GradedReflModel_Mirror)
    (frag : DefinabilityFragment M)
    (dr : DefinabilityReduction M frag) : DefinabilityCofinality M frag where
  cofinal d hex := by
    obtain ⟨x, hxd, hxsa⟩ := hex
    exact ⟨dr.red x, dr.red_canonical x,
           le_trans (dr.red_grade_le x) hxd,
           by rw [dr.red_selfApp_eq]; exact hxsa⟩

-- ============================================================
-- DescriptiveComplexityModelData (the Chain 3 AlgebraicModelData)
-- ============================================================

/-- Descriptive complexity model data: a reduction map that IS selfApp.

    The Chain 3 analog of AlgebraicModelData (Chain 5) and
    ProofComplexityModelData (Chain 2). The four fields capture that
    selfApp is an idempotent grade-non-increasing projection. From this,
    BOTH the DefinabilityFragment (cotrip) AND the DefinabilityReduction
    (cofinality) follow automatically.

    In the descriptive complexity setting, the concrete instantiation is:
    - red = formula canonicalization (NNF conversion, Hintikka type
      representative, or any idempotent normal form operation)
    - red_grade_le: canonicalization does not increase quantifier rank
    - red_idempotent: already-canonical formulas are fixed points
    - selfApp_eq_red: when M is constructed with fold = extract semantics
      and unfold = express as canonical formula, selfApp IS canonicalization

    The key insight (cross-chain pattern): cofinality was never about
    whether specific hard instance families (Tseitin, CFI graphs) require
    unbounded "four measures." It is about selfApp being a projection.
    Any overflow witness x projects via red to a canonical element with
    same grade and same selfApp — cofinality is structural.

    | DescriptiveComplexityModelData field | Concrete fact                        |
    |--------------------------------------|--------------------------------------|
    | red                                  | foCanonical (NNF conversion)         |
    | red_grade_le                         | foCanonical_depth_le (depth ≤)       |
    | red_idempotent                       | foCanonical_idempotent               |
    | selfApp_eq_red                       | selfApp IS canonicalize (by constr.) | -/
structure DescriptiveComplexityModelData (M : GradedReflModel_Mirror) where
  /-- The canonicalization map. -/
  red : M.carrier → M.carrier
  /-- Canonicalization is grade-non-increasing. -/
  red_grade_le : ∀ x, M.grade (red x) ≤ M.grade x
  /-- Canonicalization is idempotent: canonical elements are fixed. -/
  red_idempotent : ∀ x, red (red x) = red x
  /-- selfApp IS canonicalization: unfold(fold(x)) = canonical form. -/
  selfApp_eq_red : ∀ x, M.selfApp x = red x

/-- From DescriptiveComplexityModelData, derive the canonical predicate:
    an element is definability-canonical iff it is a fixed point of
    canonicalization. -/
def DescriptiveComplexityModelData.isDefinabilityCanonical {M : GradedReflModel_Mirror}
    (dcmd : DescriptiveComplexityModelData M) (x : M.carrier) : Prop :=
  dcmd.red x = x

/-- From DescriptiveComplexityModelData, construct a DefinabilityFragment.
    Cotrip: for canonical x (red x = x), selfApp(x) = red(x) = x,
    so unfold(fold(x)) = x. -/
def DescriptiveComplexityModelData.toFragment {M : GradedReflModel_Mirror}
    (dcmd : DescriptiveComplexityModelData M) : DefinabilityFragment M where
  isDefinabilityCanonical := dcmd.isDefinabilityCanonical
  cotrip_on_canonical x hx := by
    show M.selfApp x = x
    rw [dcmd.selfApp_eq_red]; exact hx

/-- From DescriptiveComplexityModelData, construct a DefinabilityReduction.
    - red produces canonical elements (by idempotence)
    - red is grade-non-increasing (given)
    - selfApp is invariant under red (selfApp = red + idempotence) -/
def DescriptiveComplexityModelData.toReduction {M : GradedReflModel_Mirror}
    (dcmd : DescriptiveComplexityModelData M) : DefinabilityReduction M dcmd.toFragment where
  red := dcmd.red
  red_canonical x := by
    show dcmd.red (dcmd.red x) = dcmd.red x
    exact dcmd.red_idempotent x
  red_grade_le := dcmd.red_grade_le
  red_selfApp_eq x := by
    show M.selfApp (dcmd.red x) = M.selfApp x
    rw [dcmd.selfApp_eq_red (dcmd.red x), dcmd.red_idempotent, ← dcmd.selfApp_eq_red]

-- ============================================================
-- Chain 3 complete bridge from DescriptiveComplexityModelData
-- ============================================================

/-- CHAIN 3 COMPLETE BRIDGE FROM DESCRIPTIVE COMPLEXITY MODEL DATA.

    DescriptiveComplexityModelData provides the full chain:
    DescriptiveComplexityModelData
    → DefinabilityFragment + DefinabilityReduction
    → DefinabilityCofinality
    → RelevantSubdomain
    → SelfAppUnbounded → False

    Exactly parallel to chain5_algebraic_bridge and
    chain2_proofcomplexity_bridge. The four fields of
    DescriptiveComplexityModelData map to concrete FO formula operations:
    - red = formula canonicalization (NNF / Hintikka type representative)
    - red_grade_le = canonicalization preserves quantifier rank
    - red_idempotent = canonical forms are fixed points
    - selfApp_eq_red = selfApp IS canonicalization (by model construction) -/
theorem chain3_descriptive_bridge
    (M : GradedReflModel_Mirror)
    (hub : SelfAppUnbounded_Mirror M)
    (dcmd : DescriptiveComplexityModelData M) : False :=
  chain3_definability_bridge M hub dcmd.toFragment
    (definabilityReduction_cofinality M dcmd.toFragment dcmd.toReduction)

/-- CHAIN 3 DIRECT BRIDGE (bypasses RelevantSubdomain).

    DescriptiveComplexityModelData gives selfApp = red and red is
    grade-non-increasing. Therefore selfApp is grade-non-increasing,
    directly contradicting SelfAppUnbounded. Uses only two of the four
    ModelData fields.

    Parallel to chain5_direct_bridge and chain2_direct_bridge. -/
theorem chain3_direct_bridge
    (M : GradedReflModel_Mirror)
    (hub : SelfAppUnbounded_Mirror M)
    (dcmd : DescriptiveComplexityModelData M) : False :=
  selfApp_nonincreasing_contradiction M hub dcmd.red dcmd.selfApp_eq_red dcmd.red_grade_le

end ClassicalConstraints
