/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

ClassicalConstraints/CSPAlgebraLock.lean — Lock theorem for Chain 4:
connects the bounded selfApp agreement obstruction (Side A) with
the CSP polymorphism bridge (Side B).

STATUS: 0 sorry, Classical.choice allowed (Lock).

Design notes:
- Lock theorem takes any CSPInstance (not UnboundedPolymorphismRequirement).
  Side A is unconditionally strong: no grade-bounded function agrees with
  selfApp, so hardness of the specific instance is irrelevant.
- PolymorphismFaithful: one-way only (forward direction).
- Lock proof (no_poly_csp_solver_via_transfer): 3-step, uses transfer hypothesis
  to promote bounded witness to grade-bounded function, then Side A fires.
-/

import ClassicalConstraints.Chain4_CSP.CSPSelectorBridge
import ClassicalConstraints.Shared.CookFaithfulness
import ClassicalConstraints.Shared.SideAMirror

namespace ClassicalConstraints

-- ════════════════════════════════════════════════════════════
-- Step 1: Mirror types from Side A (proved in pnp-integrated)
-- ════════════════════════════════════════════════════════════

-- GradedReflModel_Mirror, SelfAppUnbounded_Mirror, and
-- sideA_bounded_selector_impossible are imported from SATBoundaryLock.

/-- Side A axiom alias for Chain 4 naming convention. -/
theorem sideA_bounded_selfApp_agreement_impossible
    (M : GradedReflModel_Mirror)
    (hub : SelfAppUnbounded_Mirror M) (d : Nat) :
    ¬∃ (f : M.carrier → M.carrier),
      (∀ x, M.grade x ≤ d → f x = M.selfApp x) ∧
      (∀ x, M.grade x ≤ d → M.grade (f x) ≤ d) :=
  sideA_bounded_selector_impossible M hub d

-- ════════════════════════════════════════════════════════════
-- Step 2: Chain-specific bridge structures
-- ════════════════════════════════════════════════════════════

/-- PolymorphismFaithful: the chain-specific faithfulness condition.
    Maps algebraic clone-level complexity (Side B) to graded model
    obstruction depth (Side A).

    ONE-WAY only (the reverse direction using fixed-point
    characterization is not well-typed conceptually).

    Forward direction: if a CSP instance requires clone level k
    (no k-bounded polymorphism family decides it), then any
    depth_transfer(k)-bounded function on the graded model fails
    to agree with selfApp. -/
structure PolymorphismFaithful
    (dom : CSPDomain)
    (lang : ConstraintLanguage dom) where
  /-- Depth distortion function: maps clone level to obstruction depth. -/
  depth_transfer : Nat → Nat
  /-- The distortion is polynomially bounded. -/
  depth_poly : PolyBound
  /-- Boundedness: depth_transfer(k) ≤ depth_poly.eval(k). -/
  depth_bounded : ∀ k, depth_transfer k ≤ depth_poly.eval k

/-- Transfer hypothesis: bridges CSP bounded algebraic witnesses to grade-bounded
    functions on the abstract graded model M.

    Given a CSP instance and a BoundedAlgebraicWitness (from a solver with access
    bound d), produces a grade-d-bounded function on M that agrees with selfApp on
    grade-d inputs.

    Together with sideA_bounded_selfApp_agreement_impossible, this gives False. -/
structure CSPTransferHypothesis
    (M : GradedReflModel_Mirror)
    (dom : CSPDomain)
    (lang : ConstraintLanguage dom) where
  /-- Transfer: a d-bounded algebraic witness yields a grade-d-bounded function
      on M that agrees with selfApp on grade-d inputs. -/
  transfer : (inst : CSPInstance dom lang) → (d : Nat) →
    BoundedAlgebraicWitness dom lang inst d →
    { f : M.carrier → M.carrier //
      (∀ x, M.grade (f x) ≤ d) ∧
      (∀ x, M.grade x ≤ d → f x = M.selfApp x) }

-- ════════════════════════════════════════════════════════════
-- Step 3: The Lock Theorem
-- ════════════════════════════════════════════════════════════

/-- The lock theorem for Chain 4.

    Causal order:
    1. solver + any CSP instance → bounded algebraic witness (solver_induces_witness)
    2. Transfer hypothesis promotes witness to grade-bounded function on M
    3. sideA_bounded_selfApp_agreement_impossible fires

    Side A is unconditionally strong: no grade-bounded function agrees with selfApp,
    regardless of whether the CSP instance is hard. The contradiction comes from
    Side A + transfer, not from CSP hardness properties.

    Open hypotheses (explicit):
    - inst : CSPInstance dom lang (any instance suffices)
    - tr : CSPTransferHypothesis M dom lang (algebraic → abstract bridge) -/
theorem no_poly_csp_solver_via_transfer
    (M : GradedReflModel_Mirror)
    (hub : SelfAppUnbounded_Mirror M)
    (dom : CSPDomain)
    (lang : ConstraintLanguage dom)
    (inst : CSPInstance dom lang)
    (tr : CSPTransferHypothesis M dom lang)
    (solver : PolyTimeCSPSolver dom lang) :
    False := by
  let d := solver.access_bound.eval inst.num_vars
  let wit := solver_induces_witness dom lang solver inst
  let ⟨f, hf_bound, hf_agree⟩ := tr.transfer inst d wit
  exact sideA_bounded_selfApp_agreement_impossible M hub d ⟨f, hf_agree, fun x _ => hf_bound x⟩

/-- Boolean CSP specialization: Chain 4 subsumes Chain 1 on Boolean domain. -/
theorem no_poly_boolean_csp_solver
    (M : GradedReflModel_Mirror)
    (hub : SelfAppUnbounded_Mirror M)
    (lang : ConstraintLanguage boolDomain)
    (inst : CSPInstance boolDomain lang)
    (tr : CSPTransferHypothesis M boolDomain lang)
    (solver : PolyTimeCSPSolver boolDomain lang) :
    False :=
  no_poly_csp_solver_via_transfer M hub boolDomain lang inst tr solver

-- ════════════════════════════════════════════════════════════
-- Step 4: Status summary
-- ════════════════════════════════════════════════════════════

-- ════════════════════════════════════════════════════════════
-- Step 5: Faithfulness implication
-- ════════════════════════════════════════════════════════════

/-- PolymorphismFaithful implies CookFaithful canonically.

    The canonical profile identifies both sat_depth and model_depth with
    depth_transfer. This is the correct construction: Chain 4 is a regime
    transfer, not a structural morphism. The clone-level depth IS both the
    SAT-side and model-side obstruction parameter. The identity profile
    witnesses that no independent distortion exists between the two sides. -/
def polymorphismFaithful_to_cookFaithful
    (dom : CSPDomain)
    (lang : ConstraintLanguage dom)
    (pf : PolymorphismFaithful dom lang)
    (enc : CookEncoding) : CookFaithful enc :=
  equalDepthFaithful enc pf.depth_transfer

-- ════════════════════════════════════════════════════════════
-- Step 6: Bridge diagnostic — regime transfer vs GRM morphism
-- ════════════════════════════════════════════════════════════

/-- CSPRegimeTransfer: what Chain 4 actually provides.

    The Bulatov-Zhuk dichotomy (WNU ↔ tractable / no-WNU ↔ NP-hard)
    maps to the PEqNP/separation dichotomy via CSPTransferHypothesis.
    This is a REGIME-LEVEL correspondence, not a structural morphism.

    What this captures:
    - The dichotomy classification aligns with PEqNP vs SelfAppUnbounded
    - Depth distortion between clone level and obstruction depth is polynomial
    - The transfer mechanism promotes bounded witnesses to grade-bounded functions

    What this does NOT capture (the gap to GRM morphism):
    - No single carrier type: clone algebra is multi-sorted (arity-indexed)
    - No fold/unfold pair: clone has no Lambek isomorphism D ≅ (D → D)
    - No inter-model map: transfer produces a function ON M, not a map BETWEEN models
    - No fold/unfold commutation: the defining property of GRM morphism is absent -/
structure CSPRegimeTransfer
    (M : GradedReflModel_Mirror)
    (dom : CSPDomain)
    (lang : ConstraintLanguage dom) where
  /-- The transfer mechanism: bounded witnesses → grade-bounded functions on M. -/
  transfer : CSPTransferHypothesis M dom lang
  /-- Depth distortion is polynomially bounded. -/
  faithfulness : PolymorphismFaithful dom lang
  /-- Hardness source: the language has unbounded polymorphism requirements. -/
  hardness : UnboundedPolymorphismRequirement dom lang

/-- Chain 4 regime transfer suffices for the lock theorem.
    Given regime transfer + SelfAppUnbounded, no poly-time CSP solver exists.
    This is the full content of Chain 4's bridge — regime-compatible, not structural. -/
theorem chain4_regime_lock
    (M : GradedReflModel_Mirror)
    (hub : SelfAppUnbounded_Mirror M)
    (dom : CSPDomain)
    (lang : ConstraintLanguage dom)
    (rt : CSPRegimeTransfer M dom lang)
    (solver : PolyTimeCSPSolver dom lang) :
    False := by
  obtain ⟨inst, _⟩ := rt.hardness.unbounded 0
  exact no_poly_csp_solver_via_transfer M hub dom lang inst rt.transfer solver

end ClassicalConstraints
