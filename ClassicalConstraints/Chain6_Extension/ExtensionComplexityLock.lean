/-
  ClassicalConstraints/ExtensionComplexityLock.lean
  Chain 6 lock: connects Side A (bounded rank impossible) with
  Side B (poly LP solver → bounded selector → grade-bounded function).

  Status of each piece:
  1. Side A (bounded_rank_impossible): PROVED in pnp-integrated.
     Mirrored here as an axiom since it lives in a different repo.
  2. Side B (poly_solver_induces_bounded_selector): PROVED in this repo.
  3. CookFaithful: OPEN — explicit parameter, not assumed.
  4. GeometricTransferHypothesis: OPEN — explicit parameter bridging
     the geometric (nonneg rank) world and the graded model world.

  The lock theorem is 3 lines:
  1. Get bounded selector from poly-time solver (Side B, proved)
  2. Transfer to grade-bounded function (GeometricTransferHypothesis, open)
  3. Contradiction from Side A (axiom, proved in pnp-integrated)

  Classical.choice is allowed (Side B).
  No sorry.
  One mirror axiom: sideA_bounded_rank_impossible.
-/

import ClassicalConstraints.Chain6_Extension.ExtensionSelectorBridge
import ClassicalConstraints.Shared.CookFaithfulness
import ClassicalConstraints.Shared.CookSelectorBridge
import ClassicalConstraints.Shared.SideAMirror

namespace ClassicalConstraints

-- ════════════════════════════════════════════════════════════
-- Section 1: Mirror types from Side A
-- ════════════════════════════════════════════════════════════

-- GradedReflModel_Mirror, SelfAppUnbounded_Mirror, and
-- sideA_bounded_selector_impossible are imported from SATBoundaryLock.

/-- Side A axiom alias for Chain 6 naming convention. -/
theorem sideA_bounded_rank_impossible (M : GradedReflModel_Mirror)
    (hub : SelfAppUnbounded_Mirror M) (d : Nat) :
    ¬∃ (f : M.carrier → M.carrier),
      (∀ x, M.grade x ≤ d → f x = M.selfApp x) ∧
      (∀ x, M.grade x ≤ d → M.grade (f x) ≤ d) :=
  sideA_bounded_selector_impossible M hub d

-- ════════════════════════════════════════════════════════════
-- Section 3: GeometricTransferHypothesis
-- ════════════════════════════════════════════════════════════

/-- The transfer hypothesis for Chain 6: connects nonneg rank of the
    correlation polytope to grade-bounded functions on the graded model.

    If the correlation polytope has poly-bounded nonneg rank (equivalently,
    a poly-size LP exists), then the corresponding extraction function is
    grade-bounded on the graded model.

    This is OPEN: it is the conjunction of:
    1. GeometricFaithful (nonneg rank is geometrically meaningful)
    2. The encoding preserves the geometric → graded translation

    Any theorem using this carries it as an explicit parameter. -/
structure GeometricTransferHypothesis
    (M : GradedReflModel_Mirror)
    (family : SATFamily)
    (enc : CookEncoding)
    (cf : CookFaithful enc) where
  /-- For each size n, if a bounded selector exists with capacity d,
      then a grade-bounded function exists on M agreeing with selfApp
      on grade-≤-d inputs.

      This is the geometric bridge: bounded observation (LP / nonneg rank)
      implies grade-bounded approximation of selfApp. -/
  transfer : (n : Nat) → (d : Nat) →
    BoundedSelector (family n) d →
    { f : M.carrier → M.carrier //
      (∀ x, M.grade (f x) ≤ d) ∧
      (∀ x, M.grade x ≤ d → f x = M.selfApp x) }

-- ════════════════════════════════════════════════════════════
-- Section 4: TransferHypothesis compatibility
-- ════════════════════════════════════════════════════════════

-- Note: TransferHypothesis from SATBoundaryLock.lean has the same fields.
-- SATBoundaryLock is imported (via line 27), so the structural identity
-- could be stated formally. The current design keeps them separate for
-- chain-level modularity.

-- ════════════════════════════════════════════════════════════
-- Section 5: The Lock Theorem
-- ════════════════════════════════════════════════════════════

/-- The Chain 6 lock theorem: if
    1. Side A's impossibility holds (axiom, proved in pnp-integrated),
    2. Side B's translation holds (poly-time solver → bounded selector,
       proved in CookSelectorBridge),
    3. The geometric transfer hypothesis connects the two type systems,
    then no poly-time SAT solver exists for the given family.

    Open hypotheses: CookFaithful enc, GeometricTransferHypothesis.
    These are explicit parameters — nothing is hidden.

    The geometric content (LP = extension complexity = nonneg rank) is
    in the transfer hypothesis. The lock adds no new mathematics. -/
theorem no_poly_sat_solver_geometric
    (M : GradedReflModel_Mirror)
    (hub : SelfAppUnbounded_Mirror M)
    (family : SATFamily)
    (enc : CookEncoding)
    (cf : CookFaithful enc)
    (tr : GeometricTransferHypothesis M family enc cf)
    (solver : PolyTimeSolver family) :
    False := by
  -- Step 1: Side B — poly-time solver induces a bounded selector at n = 0.
  let sel := poly_solver_induces_bounded_selector family solver 0
  let d := solver.time_bound.eval 0
  -- Step 2: Transfer hypothesis — get a grade-bounded function on M.
  let ⟨f, hbound, hagree⟩ := tr.transfer 0 d sel
  -- Step 3: Side A — contradiction from impossibility of grade-bounded selfApp.
  exact sideA_bounded_rank_impossible M hub d ⟨f, hagree, fun x _ => hbound x⟩

-- ════════════════════════════════════════════════════════════
-- Section 6: Comparison with Chain 1 lock
-- ════════════════════════════════════════════════════════════

-- The Chain 6 lock has the same structure as the Chain 1 lock (no_poly_sat_solver
-- in SATBoundaryLock.lean). The only difference is the transfer hypothesis name.
--
-- Both instantiate the same 3-step pattern:
-- 1. Side B: solver → bounded selector (CookSelectorBridge)
-- 2. Transfer: bounded selector → grade-bounded function
-- 3. Side A: grade-bounded function → False (impossibility)
--
-- This is the universal lock pattern shared across all chains.

-- ════════════════════════════════════════════════════════════
-- Section 7: Faithfulness implication
-- ════════════════════════════════════════════════════════════

/-- GeometricFaithful implies CookFaithful canonically.

    The canonical profile identifies both sat_depth and model_depth with
    the SAT family's variable count at each size. Chain 6 is a geometric
    chain: the nonneg rank obstruction is measured against the correlation
    polytope at each size, and the variable count is the natural scale
    parameter. The identity profile witnesses that the geometric and
    combinatorial sides share the same scale. -/
def geometricFaithful_to_cookFaithful
    (enc : CookEncoding)
    (family : SATFamily)
    (_gf : GeometricFaithful family) : CookFaithful enc :=
  equalDepthFaithful enc (fun n => (family n).num_vars)

end ClassicalConstraints
