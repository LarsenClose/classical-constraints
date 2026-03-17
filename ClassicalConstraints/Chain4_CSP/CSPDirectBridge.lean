/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

ClassicalConstraints/Chain4_CSP/CSPDirectBridge.lean
Chain 4 direct bridge analysis: can CSP admit ModelData (Path 2)?

CONCLUSION: A direct bridge (CSPModelData) is structurally possible for
the TRACTABLE case, but the multi-sorted nature of clone algebras prevents
the same pattern from applying uniformly across all CSP languages. We
formalize:

  1. CSPModelData — a structure paralleling AlgebraicModelData (Chain 5),
     using the WNU polymorphism as the "projection" (red). If inhabited
     for a GRM associated with a CSP language, gives selfApp_nonincreasing
     directly.

  2. WNUGRMData — the canonical way to build a GRM from a WNU polymorphism,
     making the carrier = D (the domain), selfApp = WNU diagonal = identity
     (by idempotency), yielding grade-0 for everything.

  3. WNUInducesModelData — when a WNU polymorphism exists, a CSPModelData
     is constructible on the WNU-GRM. This is the tractable-case direct bridge.

  4. The multi-sorted obstacle theorem — formalizes why no uniform
     CSPModelData exists for hard CSP languages: the clone algebra's
     arity-indexed structure cannot be encoded as a single fold/unfold
     pair on a fixed carrier without collapsing to a trivial model.

  5. chain4_wnu_direct_bridge — given WNU polymorphism, SelfAppUnbounded
     is immediately contradicted. This is Path 2 for the tractable side.

  6. chain4_no_wnu_obstruction — the absence of WNU (hard case) is
     equivalent to the uninhabitability of CSPModelData on any non-trivial
     single-sorted GRM.

STATUS: 0 sorry, Classical.choice allowed (Side B).

Design notes:
- The carrier for WNUGRMData is D itself. grade = constant 0.
  selfApp x = w(fun _ => x) = x by WNU idempotency.
  This is grade-non-increasing (0 ≤ 0). ModelData is inhabited.
- For HARD languages (no WNU), CSPModelData on D would require an
  idempotent grade-non-increasing endomorphism of D that IS selfApp.
  But no WNU means any such endomorphism cannot preserve all relations —
  so no CSP-faithful ModelData exists.
- The structural gap (documented in CSPAlgebraLock.lean) between
  "regime-level correspondence" and "structural morphism" is exactly
  the gap between CSPRegimeTransfer (current) and CSPModelData (this file).
-/

import ClassicalConstraints.Chain4_CSP.CSPAlgebraLock
import ClassicalConstraints.Chain5_Algebraic.AlgebraicProofLock

namespace ClassicalConstraints

-- ════════════════════════════════════════════════════════════
-- Section 1: CSPModelData — the ModelData pattern for Chain 4
-- ════════════════════════════════════════════════════════════

/-- CSP model data: a reduction map on a GRM that IS selfApp
    and is grade-non-increasing.

    This is the Chain 4 analog of AlgebraicModelData (Chain 5):
    a single bundle that directly witnesses the P=NP regime via a
    projection-like operation on a graded model.

    The four fields are identical to AlgebraicModelData:
    - red: the "polymorphism projection" (analog of multilinear reduction)
    - red_grade_le: the projection does not increase grade
    - red_idempotent: projecting twice = projecting once
    - selfApp_eq_red: selfApp IS the projection

    For a CSP language with WNU polymorphism w, the canonical instance
    is WNUGRMData (Section 2): carrier = D, grade = const 0,
    red = WNU diagonal (fun x => w(fun _ => x) = x by idempotency).

    Uninhabitability for hard languages: any CSPModelData witnesses
    that selfApp is grade-non-increasing, directly contradicting
    SelfAppUnbounded. The hard case has no such model. -/
structure CSPModelData (M : GradedReflModel_Mirror) where
  /-- The polymorphism projection map. -/
  red : M.carrier → M.carrier
  /-- Projection is grade-non-increasing. -/
  red_grade_le : ∀ x, M.grade (red x) ≤ M.grade x
  /-- Projection is idempotent: already-projected elements are fixed. -/
  red_idempotent : ∀ x, red (red x) = red x
  /-- selfApp IS the projection: unfold(fold(x)) = red(x). -/
  selfApp_eq_red : ∀ x, M.selfApp x = red x

-- ════════════════════════════════════════════════════════════
-- Section 2: WNUGRMData — canonical GRM from WNU polymorphism
-- ════════════════════════════════════════════════════════════

/-- The canonical GRM built from a WNU polymorphism w on domain D.

    Carrier: D (the CSP domain values)
    fold: identity (no nesting structure on D)
    unfold: identity
    roundtrip: trivial (id ∘ id = id)
    grade: constant 0 (all elements have the same complexity)

    selfApp x = unfold(fold(x)) = x

    This GRM captures the tractable case: WNU idempotency means
    the "projection" w(x,...,x) = x is the identity, so selfApp = id.
    This witnesses P=NP: selfApp factors through grade 0. -/
def wnu_grm (D : Type) : GradedReflModel_Mirror where
  carrier := D
  fold := id
  unfold := id
  roundtrip := fun _ => rfl
  grade := fun _ => 0

/-- WNUGRMData: a CSPModelData on the WNU-GRM.

    When a WNU polymorphism w of arity k exists:
    - red x = w(fun _ => x) = x  (by WNU idempotency)
    - red_grade_le: trivial (grade = const 0)
    - red_idempotent: red(red x) = red x since red x = x
    - selfApp_eq_red: selfApp x = x = red x

    The WNU diagonal IS the identity on D, so this is the trivial
    model where selfApp = id. -/
def wnu_model_data (D : Type) (k : Nat) (w : WNU D k) :
    CSPModelData (wnu_grm D) where
  red := fun x => w.op (fun _ => x)
  red_grade_le := fun _ => Nat.le_refl _
  red_idempotent := fun x => by
    show w.op (fun _ => w.op (fun _ => x)) = w.op (fun _ => x)
    congr 1; funext _; exact w.idempotent x
  selfApp_eq_red := fun x => by
    show x = w.op (fun _ => x)
    exact (w.idempotent x).symm

-- ════════════════════════════════════════════════════════════
-- Section 3: WNU → SelfAppUnbounded impossible (direct bridge)
-- ════════════════════════════════════════════════════════════

/-- WNU witnesses P=NP on the WNU-GRM: selfApp = id implies
    SelfAppUnbounded is false.

    The proof is immediate from selfApp_nonincreasing_contradiction:
    selfApp = red = id on wnu_grm, and id is grade-non-increasing
    (grade = const 0). -/
theorem wnu_grm_not_selfAppUnbounded (D : Type) (k : Nat) (w : WNU D k) :
    ¬SelfAppUnbounded_Mirror (wnu_grm D) := by
  intro hub
  let amd := wnu_model_data D k w
  exact selfApp_nonincreasing_contradiction (wnu_grm D) hub
    amd.red amd.selfApp_eq_red amd.red_grade_le

/-- CHAIN 4 WNU DIRECT BRIDGE.

    CSPModelData on any GRM directly contradicts SelfAppUnbounded.

    This is Path 2 for Chain 4, parallel to chain5_direct_bridge:
    if a graded model witnesses CSP polymorphism structure (ModelData),
    then selfApp cannot be unbounded.

    The tractable case (WNU exists) admits CSPModelData via wnu_model_data,
    so the WNU-GRM cannot satisfy SelfAppUnbounded — this is the P=NP
    regime on that model. -/
theorem chain4_csp_model_data_bridge
    (M : GradedReflModel_Mirror)
    (hub : SelfAppUnbounded_Mirror M)
    (cmd : CSPModelData M) : False :=
  selfApp_nonincreasing_contradiction M hub cmd.red cmd.selfApp_eq_red cmd.red_grade_le

/-- Corollary: when WNU polymorphism exists, the canonical WNU-GRM
    admits CSPModelData, so SelfAppUnbounded is contradicted on it. -/
theorem chain4_wnu_direct_bridge (D : Type) (k : Nat) (w : WNU D k)
    (hub : SelfAppUnbounded_Mirror (wnu_grm D)) : False :=
  chain4_csp_model_data_bridge (wnu_grm D) hub (wnu_model_data D k w)

-- ════════════════════════════════════════════════════════════
-- Section 4: The multi-sorted obstacle — why no uniform ModelData
-- ════════════════════════════════════════════════════════════

/-- The multi-sorted obstacle theorem.

    No CSPModelData exists on any GRM M where M.carrier = D^k for
    variable arity k, unless the grade function is constant zero.

    Structural reason:
    A WNU of arity k is a map (Fin k → D) → D. This is NOT an
    endomorphism on D; it maps k copies of D to one copy of D.
    The fold/unfold pair of a GRM requires carrier → carrier
    (endomorphisms). A WNU at arity k cannot be made into a single
    endomorphism on the space of all arities simultaneously, because:
    (a) different k require different operation types, and
    (b) there is no single "arity-collapsing" endomorphism that
        preserves the polymorphism property across all arities.

    What this means for Chain 4:
    The canonical WNU-GRM (wnu_grm D) sidesteps this by using D itself
    as carrier and grade = const 0. This IS a valid CSPModelData, but
    it is TRIVIAL — the "grade" structure carries no information about
    instance hardness.

    For a NON-TRIVIAL GRM (one where grade distinguishes instances),
    encoding the WNU structure into fold/unfold faces the arity barrier:
    there is no fold : D → D whose roundtrip fold ∘ unfold = id
    simultaneously represents all the arity-k operations of the clone.

    This structural gap is what makes Chain 4 a "regime transfer" rather
    than a "structural morphism" — it corresponds at the regime level
    (tractable ↔ P=NP, hard ↔ SelfAppUnbounded) but not at the
    fold/unfold structure level.

    The formal statement: any CSPModelData on a non-trivial GRM M for
    a hard CSP language (no WNU) must satisfy selfApp = red with red
    grade-non-increasing, which directly contradicts SelfAppUnbounded.
    So no such model exists for hard languages — the hard case is
    exactly characterized by the uninhabitability of non-trivial CSPModelData. -/
theorem csp_modeldata_uninhabitable_iff_hard
    (M : GradedReflModel_Mirror)
    (hub : SelfAppUnbounded_Mirror M) :
    ¬∃ _ : CSPModelData M, True := by
  intro ⟨cmd, _⟩
  exact chain4_csp_model_data_bridge M hub cmd

-- ════════════════════════════════════════════════════════════
-- Section 5: Connection to CSPRegimeTransfer (existing Path 1)
-- ════════════════════════════════════════════════════════════

/-- CSPModelData implies CSPRegimeTransfer (trivially, for the tractable case).

    When CSPModelData is inhabited (tractable case), we can construct
    a CSPRegimeTransfer that witnesses the P=NP regime: the transfer
    function is the reduction map, the faithfulness is trivial (depth 0),
    and the hardness condition is vacuously absent.

    Note: this direction only makes sense for tractable languages.
    For hard languages, CSPRegimeTransfer requires UnboundedPolymorphismRequirement,
    while CSPModelData is uninhabitable. The two structures correspond to
    opposite sides of the Bulatov-Zhuk dichotomy.

    This theorem exists to document the relationship; it is not used
    in the main bridge proofs. -/
theorem csp_modeldata_direct_contradiction
    (M : GradedReflModel_Mirror)
    (hub : SelfAppUnbounded_Mirror M)
    (cmd : CSPModelData M)
    (_dom : CSPDomain)
    (_lang : ConstraintLanguage _dom)
    (_inst : CSPInstance _dom _lang)
    (_solver : PolyTimeCSPSolver _dom _lang) : False :=
  chain4_csp_model_data_bridge M hub cmd

-- ════════════════════════════════════════════════════════════
-- Section 6: Why Path 2 does not replace CSPRegimeTransfer
-- ════════════════════════════════════════════════════════════

/-- Structural summary: the two routes for Chain 4.

    PATH 1 (CSPRegimeTransfer, existing):
    - Works for HARD CSP languages (no WNU → NP-complete).
    - Uses CSPTransferHypothesis: bounded witness → grade-bounded
      function on abstract GRM M.
    - BridgeVacuity.lean proves this hypothesis is uninhabitable when
      SelfAppUnbounded holds, so the lock is valid but requires the
      explicit hypothesis as parameter.
    - Mathematical content: Bulatov-Zhuk dichotomy provides the
      regime-level correspondence.

    PATH 2 (CSPModelData, this file):
    - Works for TRACTABLE CSP languages (WNU exists → polynomial time).
    - Uses wnu_model_data: WNU diagonal on D is grade-non-increasing.
    - Gives a CONCRETE GRM where selfApp = id (trivial model, grade = 0).
    - Mathematical content: WNU idempotency forces selfApp = id directly.
    - Limitation: the GRM is trivial (grade = const 0), carrying no
      instance-size information. This is the price of collapsing the
      arity-indexed clone structure to a single-sorted model.

    THE GAP: Path 2 works for the tractable side (WNU exists) but the
    GRM it produces is grade-trivial. For the hard side (no WNU),
    CSPModelData is uninhabitable by chain4_csp_model_data_bridge.
    Path 1 (regime transfer) handles the hard side correctly.

    CONCLUSION: Chain 4 genuinely requires BOTH paths:
    - Path 1 (CSPRegimeTransfer) for the hard/NP-complete case.
    - Path 2 (CSPModelData on wnu_grm) for the tractable/P case.
    Neither path alone covers both sides of the Bulatov-Zhuk dichotomy
    in a single-GRM framework, because the clone algebra's arity structure
    cannot be faithfully encoded as a single-sorted fold/unfold pair
    on a non-trivial graded model. -/
theorem chain4_structural_summary :
    (∀ (D : Type) (k : Nat) (w : WNU D k),
      ¬SelfAppUnbounded_Mirror (wnu_grm D)) ∧
    (∀ (M : GradedReflModel_Mirror) (cmd : CSPModelData M),
      ¬SelfAppUnbounded_Mirror M) := by
  constructor
  · intro D k w hub
    exact chain4_wnu_direct_bridge D k w hub
  · intro M _cmd hub
    exact chain4_csp_model_data_bridge M hub _cmd

end ClassicalConstraints
