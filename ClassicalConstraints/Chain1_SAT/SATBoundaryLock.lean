/-
  ClassicalConstraints/SATBoundaryLock.lean
  The lock: connects Side A (bounded selector impossible) with
  Side B (poly solver induces bounded selector).

  Status of each piece:
  1. Side A (bounded_selector_impossible): PROVED in pnp-integrated.
     Mirrored here as an axiom since it lives in a different repo.
  2. Side B (poly_solver_induces_bounded_selector): PROVED in this repo.
  3. CookFaithful: OPEN — explicit parameter, not assumed.
  4. TransferHypothesis: OPEN — explicit parameter bridging the two
     type systems (graded model vs SAT instances).

  If you accept all four, then: no poly-time SAT solver exists for
  families with sufficient obstruction depth, i.e., P ≠ NP follows.
  The open questions (3, 4) are isolated in CookFaithfulness.lean
  and the TransferHypothesis structure below.
-/

import ClassicalConstraints.Shared.SideAMirror
import ClassicalConstraints.Shared.CookSelectorBridge
import ClassicalConstraints.Shared.CookFaithfulness

namespace ClassicalConstraints

-- GradedReflModel_Mirror, GradedReflModel_Mirror.selfApp,
-- SelfAppUnbounded_Mirror, sideA_bounded_selector_impossible
-- are imported from SideAMirror.

-- ============================================================
-- Transfer hypothesis: bridges SAT types to graded model types
-- ============================================================

/-- The transfer hypothesis connects the SAT-instance world (Side B)
    with the graded reflexive model world (Side A). This is OPEN:
    proving it requires showing that Cook encoding faithfully maps
    bounded selectors into grade-bounded functions on the model.

    Any theorem using this carries it as an explicit parameter. -/
structure TransferHypothesis
    (M : GradedReflModel_Mirror)
    (family : SATFamily)
    (enc : CookEncoding)
    (cf : CookFaithful enc) where
  /-- For each size n, a poly-bounded selector on (family n) yields
      a grade-bounded function on M that agrees with selfApp on
      grade-≤-d inputs. The contradiction then follows from Side A. -/
  transfer : (n : Nat) → (d : Nat) →
    BoundedSelector (family n) d →
    { f : M.carrier → M.carrier //
      (∀ x, M.grade (f x) ≤ d) ∧
      (∀ x, M.grade x ≤ d → f x = M.selfApp x) }

-- ============================================================
-- The Lock Theorem
-- ============================================================

/-- The lock: if Side A's impossibility holds (axiom, proved elsewhere),
    Side B's translation holds (proved in CookSelectorBridge), and the
    transfer hypothesis connects the two type systems, then no poly-time
    SAT solver exists.

    Open hypotheses: CookFaithful enc, TransferHypothesis M family enc cf.
    These are explicit parameters — nothing is hidden. -/
theorem no_poly_sat_solver
    (M : GradedReflModel_Mirror)
    (hub : SelfAppUnbounded_Mirror M)
    (family : SATFamily)
    (enc : CookEncoding)
    (cf : CookFaithful enc)
    (tr : TransferHypothesis M family enc cf)
    (solver : PolyTimeSolver family) :
    False := by
  -- Pick n = 0, get the bounded selector from Side B
  let sel := poly_solver_induces_bounded_selector family solver 0
  let d := solver.time_bound.eval 0
  -- Transfer to a grade-bounded function on M agreeing with selfApp
  let ⟨f, hbound, hagree⟩ := tr.transfer 0 d sel
  -- Side A says this is impossible
  exact sideA_bounded_selector_impossible M hub d ⟨f, hagree, fun x _ => hbound x⟩

end ClassicalConstraints
