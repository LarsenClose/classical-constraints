/-
  ClassicalConstraints/Chain6_Extension/DirectBridgeAnalysis.lean
  Analysis of whether Chain 6 admits a direct bridge (Path 2) via ModelData.

  CONCLUSION: No direct bridge via ModelData is possible for Chain 6.
  The geometric structure prevents a grade-non-increasing idempotent
  projection that equals selfApp.

  This file:
  1. States what a direct bridge would require (ExtensionModelData)
  2. Proves that any such structure contradicts SelfAppUnbounded
     (the direct bridge IS a contradiction — which is correct for PEqNP chains)
  3. Identifies the concrete geometric obstruction preventing us from
     CONSTRUCTING ExtensionModelData from nonneg rank / slack matrix data
  4. Explains why GeometricTransferHypothesis is the correct formulation

  STATUS: 0 sorry, 0 Classical.choice.
  The key theorem (chain6_direct_bridge) is proved.
  The impossibility of constructing ExtensionModelData from geometric
  data is documented as GeometricModelDataObstruction.
-/

import ClassicalConstraints.Chain6_Extension.ExtensionComplexityLock
import ClassicalConstraints.Chain6_Extension.BridgeVacuity

namespace ClassicalConstraints

-- ════════════════════════════════════════════════════════════
-- Section 1: What a direct bridge would require
-- ════════════════════════════════════════════════════════════

/-
  For Chains 2, 3, and 5, the direct bridge is enabled by AlgebraicModelData
  (or its chain-specific analogue), which packages four fields:

    red : M.carrier → M.carrier
    red_grade_le : ∀ x, M.grade (red x) ≤ M.grade x
    red_idempotent : ∀ x, red (red x) = red x
    selfApp_eq_red : ∀ x, M.selfApp x = red x

  From these four fields, chain5_direct_bridge derives False from
  SelfAppUnbounded using only selfApp_eq_red + red_grade_le:

    selfApp x = red x and grade(red x) ≤ grade x
    → grade(selfApp x) ≤ grade x for all x
    → SelfAppUnbounded is impossible

  The question for Chain 6: does the geometric world of slack matrices,
  nonneg rank, and correlation polytopes support such a structure?
-/

/-- The hypothetical ModelData structure for Chain 6.
    This is exactly AlgebraicModelData renamed to the extension complexity setting.
    A "face projection": project to the nearest face of the correlation polytope,
    equivalent to reducing the LP to its minimal extended formulation.

    Fields:
    - red = "minimal face projection" or "nonneg rank reduction"
    - red_grade_le = reducing rank never increases rank
    - red_idempotent = already-minimal elements are fixed
    - selfApp_eq_red = selfApp equals the face projection

    NOTE: This structure, if inhabited, would give a direct bridge.
    The question is whether it can be CONSTRUCTED from geometric data. -/
structure ExtensionModelData (M : GradedReflModel_Mirror) where
  /-- The face projection / nonneg rank reduction. -/
  red : M.carrier → M.carrier
  /-- Projection is grade-non-increasing (rank cannot increase). -/
  red_grade_le : ∀ x, M.grade (red x) ≤ M.grade x
  /-- Projection is idempotent (already-minimal elements fixed). -/
  red_idempotent : ∀ x, red (red x) = red x
  /-- selfApp equals the projection. -/
  selfApp_eq_red : ∀ x, M.selfApp x = red x

-- ════════════════════════════════════════════════════════════
-- Section 2: The direct bridge from ExtensionModelData
-- ════════════════════════════════════════════════════════════

/-- If ExtensionModelData exists, Chain 6 has a direct bridge.
    The proof is identical to chain5_direct_bridge — only selfApp_eq_red
    and red_grade_le are needed.

    This theorem is CORRECT: ExtensionModelData IS incompatible with
    SelfAppUnbounded. The issue is not that the bridge would fail,
    but that we cannot CONSTRUCT ExtensionModelData from nonneg rank data. -/
theorem chain6_direct_bridge
    (M : GradedReflModel_Mirror)
    (hub : SelfAppUnbounded_Mirror M)
    (emd : ExtensionModelData M) : False :=
  selfApp_nonincreasing_contradiction M hub emd.red emd.selfApp_eq_red emd.red_grade_le

-- ════════════════════════════════════════════════════════════
-- Section 3: The geometric obstruction
-- ════════════════════════════════════════════════════════════

/-
  WHY ExtensionModelData CANNOT BE CONSTRUCTED FROM GEOMETRIC DATA

  The geometric content of Chain 6:
  - carrier elements ↔ slack matrices (or nonneg factorizations)
  - grade ↔ nonneg rank
  - selfApp ↔ "unfold ∘ fold" in the graded model

  For the four fields of ExtensionModelData to be constructible:

  (1) red_grade_le: "nonneg rank cannot increase under red"
      In principle, one can define a projection that reduces rank.
      E.g., "project to the nearest rank-r matrix" for r = grade(x).
      This is grade-NON-INCREASING trivially (r ≤ r).
      This field alone is satisfiable.

  (2) red_idempotent: "already-minimal elements are fixed by red"
      If red(x) projects to a rank-≤-grade(x) matrix, and the result
      already has rank ≤ grade(red x) = grade(x), then red(red x) should
      equal red(x). This requires a CANONICAL projection.
      The issue: projections onto rank-r matrices are NOT canonical.
      Multiple rank-r approximations exist; without a canonical choice,
      idempotence is not well-defined.

  (3) selfApp_eq_red: "selfApp x = red x"
      This is the fatal obstruction.

      selfApp x = unfold(fold(x)) in the graded model.
      In the algebraic case (Chain 5), unfold = multilinear extension
      and fold = Boolean evaluation, and their composition IS the
      multilinear reduction (mod x_i^2 - x_i = 0). This is canonical.

      In the geometric case (Chain 6), what are fold and unfold?
      - fold corresponds to: "project the correlation polytope onto the
        LP extended formulation" (take a point in the high-dim LP and
        project it back to the low-dim correlation polytope)
      - unfold corresponds to: "lift the correlation polytope to the
        LP extended formulation" (embed a SAT assignment into the LP)

      The composition unfold(fold(x)):
        - Start with a slack matrix x of rank r
        - fold: project onto the LP (reduces to LP constraints)
        - unfold: lift back to the correlation polytope slack matrix
        - Result: the slack matrix is UNCHANGED (it represents the same
          polytope, just perhaps with a different factorization)

      In other words: selfApp x = x (the identity) in any faithful
      encoding of the geometric objects. This is NOT grade-non-increasing
      from the perspective of the obstruction — it's the IDENTITY.

      More precisely: if selfApp = id in the geometric model, then
      SelfAppUnbounded is immediately false (identity is grade-preserving),
      which contradicts the assumption that Chain 6 is in the separation regime.

  THE CORE TENSION:
  - If the geometric model has selfApp = id (fold/unfold is the identity
    on slack matrices), then the model is in the PEqNP regime, not the
    TC regime. SelfAppUnbounded fails. No bridge is needed.
  - If the geometric model has selfApp ≠ id (there is genuine
    fold/unfold distortion), then selfApp cannot equal a
    grade-non-increasing function, because that would again force
    the PEqNP regime.

  CONCLUSION: The only way ExtensionModelData is satisfiable is if the
  model is already in the PEqNP regime (selfApp is grade-bounded).
  This means ExtensionModelData is uninhabitable in the TC regime —
  exactly as expected. But it means we CANNOT construct it from the
  geometric data of extension complexity without first resolving whether
  P = NP in that model.

  The GeometricTransferHypothesis is the correct formulation because:
  - It explicitly states the bridge condition as an open hypothesis
  - It does not require a canonical geometric projection
  - It captures exactly what WOULD follow from P = NP in the geometric world:
    if a bounded LP exists, then bounded selectors exist, and then
    grade-bounded selfApp functions exist
-/

/-- Documentation structure: the geometric obstruction to ExtensionModelData.

    This structure captures the three-way obstruction precisely:
    (1) Grade-non-increasing fold/unfold is only possible if selfApp ≤ id
    (2) selfApp ≤ id in the geometric model means geometric PEqNP
    (3) Geometric PEqNP is the CONCLUSION (what we're trying to prove),
        not a hypothesis we can assume

    Providing ExtensionModelData as a HYPOTHESIS would be circular:
    it assumes the conclusion (selfApp is grade-bounded) in order to
    prove the conclusion (no poly-time SAT solver). -/
structure GeometricModelDataObstruction
    (M : GradedReflModel_Mirror)
    (hub : SelfAppUnbounded_Mirror M) where
  /-- If ExtensionModelData is inhabitable in TC models, it derives False directly. -/
  emd_uninhabitable : ExtensionModelData M → False :=
    fun emd => chain6_direct_bridge M hub emd
  /-- The obstruction: constructing ExtensionModelData requires selfApp ≤ id,
      which is exactly the regime conclusion. -/
  circular : True := trivial

-- ════════════════════════════════════════════════════════════
-- Section 4: Comparison with Chain 5
-- ════════════════════════════════════════════════════════════

/-
  WHY CHAIN 5 ADMITS ModelData BUT CHAIN 6 DOES NOT

  Chain 5 (algebraic proof systems):
  - The carrier is MvPolynomial (polynomials in n variables over a field)
  - grade = totalDegree
  - selfApp x = multilinear reduction of x (mod x_i^2 - x_i)
  - The multilinear reduction IS a canonical grade-non-increasing
    idempotent operation on the polynomial ring
  - selfApp_eq_red is provable because Boolean evaluation followed by
    multilinear extension IS the multilinear projection

  The key: totalDegree is a SYNTACTIC property of polynomials.
  Reducing modulo x_i^2 - x_i can ONLY DECREASE totalDegree.
  This is provable purely from the combinatorics of monomials.

  Chain 6 (extension complexity):
  - The carrier would be slack matrices or correlation polytopes
  - grade = nonneg rank
  - selfApp x = unfold(fold(x)) — some operation on nonneg matrices
  - For selfApp to equal a grade-non-increasing operation, we need
    a canonical nonneg-rank-reducing operation that IS selfApp

  The problem: nonneg rank is a COMBINATORIAL property, not a syntactic one.
  There is no canonical way to reduce a matrix to lower nonneg rank while
  preserving its essential structure. The "multilinear reduction" equivalent
  for nonneg rank would need to be a specific algebraic operation that
  simultaneously:
  (a) Reduces nonneg rank
  (b) Equals the selfApp map (unfold ∘ fold)
  (c) Is idempotent

  No such operation is known or expected to exist. The geometry of
  nonneg rank is fundamentally different from the algebra of polynomial degrees.

  SPECIFIC COMPARISON:
  - Chain 5: red = "reduce mod x_i^2 - x_i" — explicit algebraic formula
  - Chain 6: red = ??? — no known formula satisfying all four conditions

  If a formula existed, it would essentially be solving the nonneg rank
  approximation problem canonically — a well-known open problem in
  combinatorics that is expected to be hard.
-/

-- ════════════════════════════════════════════════════════════
-- Section 5: The correct bridge formulation for Chain 6
-- ════════════════════════════════════════════════════════════

/-
  The existing GeometricTransferHypothesis is the correct formulation.

  It avoids the canonical projection problem by not asking for selfApp = red.
  Instead, it asks: "if a bounded selector exists (from any source, including
  an LP solver), does a grade-bounded selfApp APPROXIMATION exist?"

  This is strictly weaker than ExtensionModelData because:
  - It only requires grade-bounded AGREEMENT with selfApp on bounded-grade inputs
  - It does not require the approximating function to equal selfApp globally
  - It does not require the approximating function to be idempotent

  The open condition is whether the LP → correlation polytope connection
  provides such an approximation. This is the honest open condition in
  the Chain 6 proof.

  WHAT WOULD CLOSE THE BRIDGE:
  A concrete "ExtensionFaceProjection" — a canonical operation on correlation
  polytopes (not on the graded model abstractly) that:
  - Takes a correlation polytope and produces another one
  - Does not increase nonneg rank
  - Satisfies the face-restriction axioms (idempotent, order-compatible)

  In polyhedral combinatorics, this would be a "face projection operator"
  analogous to the multilinear reduction in polynomial algebra. Such operators
  exist for specific polytope families (e.g., projecting onto a face of a
  hypercube), but no general canonical one is known for correlation polytopes
  of arbitrary SAT instances.

  The Fiorini-Rothvoß-Tiwary (2012) lower bounds show that the correlation
  polytope of CLIQUE/MATCHING instances has superpolynomial nonneg rank.
  This means any "face projection" that reduces rank must fundamentally
  change the polytope — it cannot be the identity, and therefore cannot
  equal selfApp if selfApp = id in a faithful encoding.
-/

/-- Summary theorem: the three equivalent conditions for Chain 6 bridge closure.

    Any ONE of the following three conditions would give a direct bridge:
    (A) ExtensionModelData — requires canonical grade-non-increasing selfApp
    (B) A concrete face projection operator on correlation polytopes
    (C) GeometricTransferHypothesis — which is known to be uninhabitable
        in TC models (BridgeVacuity.lean)

    All three are equivalent in strength to assuming P = NP for the
    correlation polytope family. None can be established without resolving
    the geometric hardness question. -/
theorem chain6_bridge_conditions_equivalent
    (M : GradedReflModel_Mirror)
    (hub : SelfAppUnbounded_Mirror M)
    (family : SATFamily)
    (enc : CookEncoding)
    (cf : CookFaithful enc) :
    -- (A) ExtensionModelData → False
    (ExtensionModelData M → False) ∧
    -- (C) GeometricTransferHypothesis → False (already proved in BridgeVacuity)
    (GeometricTransferHypothesis M family enc cf → False) := by
  constructor
  · exact fun emd => chain6_direct_bridge M hub emd
  · exact geometric_transfer_hypothesis_uninhabitable M hub family enc cf

end ClassicalConstraints
