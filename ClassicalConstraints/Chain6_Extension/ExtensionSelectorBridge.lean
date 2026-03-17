/-
  ClassicalConstraints/ExtensionSelectorBridge.lean
  Bridge between poly-size LP formulations and nonneg rank / extension complexity.

  This file has two lanes:
  1. Geometric lane: poly-size LP → low nonneg rank (via Yannakakis).
     This is the native content of Chain 6.
  2. Computational corollary: poly-time SAT solver → poly-size LP (open hypothesis)
     → low nonneg rank → contradiction with GeometricFaithful.
     This is an OPTIONAL add-on, not the core chain.

  The geometric lane does NOT depend on PolyTimeImpliesPolyLP.
  PolyTimeImpliesPolyLP is an explicit open hypothesis, used only in the
  optional computational corollary at the end.

  Chain 6, Side B.

  Classical.choice is allowed (Side B).
  No sorry.
-/

import ClassicalConstraints.Chain6_Extension.SlackMatrixCore
import ClassicalConstraints.Chain6_Extension.SATPolytopeCore
import ClassicalConstraints.Chain6_Extension.NonnegRankObstruction
import ClassicalConstraints.Shared.CookSelectorBridge

namespace ClassicalConstraints

open SATInstance

-- ════════════════════════════════════════════════════════════
-- Section 1: GeometricFaithful
-- ════════════════════════════════════════════════════════════

/-- GeometricFaithful: the chain-specific hardness condition.

    A family of SAT instances for which the nonneg rank of the correlation
    polytope's slack matrix grows superpolynomially.

    This is OPEN — an explicit hypothesis, not assumed globally.
    It says: for a specific SAT family, no polynomial in n bounds the
    nonneg rank of the slack matrix of the correlation polytope at size n.

    Note: This does NOT include a polynomial upper bound on nonneg rank.
    Saying the rank is superpolynomial means it exceeds every fixed polynomial,
    full stop. Adding an upper polynomial bound would make the structure
    inconsistent. -/
structure GeometricFaithful (family : SATFamily) where
  /-- A family of correlation polytopes, one per size. -/
  polytopes : SATFamilyPolytope family
  /-- For each size n, the Yannakakis theorem holds for the correlation polytope.
      Carried as a structure field because Yannakakis is a deep result. -/
  yannakakis : ∀ n, YannakakisTheorem (polytopes.polytopes n).polytope
  /-- The nonneg rank is superpolynomial: no polynomial suffices to bound it.
      This is the key geometric hardness condition. -/
  h_hard_family : ∀ p : PolyBound,
    ∃ n, ¬hasNonnegRankAtMost
      (slackMatrix (polytopes.polytopes n).polytope) (p.eval n)

-- ════════════════════════════════════════════════════════════
-- Section 2: LPBoundedSelector
-- ════════════════════════════════════════════════════════════

/-- An LP-based bounded selector: the LP formulation induces a bounded
    observation window on the SAT instance's assignments.

    The key insight: an LP solver with r constraints factors the
    satisfiability decision through at most r constraint patterns.
    This gives a BoundedSelector with capacity r. -/
structure LPBoundedSelector (phi : SATInstance) (capacity : Nat) where
  /-- The underlying LP formulation. -/
  lp : LPFormulation phi
  /-- The LP size is bounded by the capacity. -/
  h_bounded : lp.num_constraints ≤ capacity
  /-- The induced selector: the LP's feasibility determines satisfiability. -/
  selector : BoundedSelector phi capacity
  /-- The selector is correct. -/
  h_correct : ∀ a, selector.select a = phi.instanceSatisfied a

-- ════════════════════════════════════════════════════════════
-- Section 3: PolyTimeImpliesPolyLP (optional computational hypothesis)
-- ════════════════════════════════════════════════════════════

/-- The hypothesis that poly-time SAT solving implies poly-size LP.
    This connects the computational (BoundedSelector) world to the
    geometric (nonneg rank) world.

    This is a structural hypothesis because the full proof requires
    showing that poly-time computation is LP-representable — a connection
    that is related to P vs NP itself.

    DESIGN NOTE: This hypothesis is used ONLY in the optional computational
    corollary (geometric_chain_no_poly_solver_computational). The core geometric
    lock (no_poly_lp_from_hard_instances) does NOT require it. -/
structure PolyTimeImpliesPolyLP (family : SATFamily) where
  /-- A poly-time solver induces a poly-size LP. -/
  solver_to_lp : PolyTimeSolver family → PolyLPSolver family
  /-- The LP size is polynomially related to the solver's time bound. -/
  h_size_relation : ∀ (solver : PolyTimeSolver family),
    ∃ p : PolyBound, ∀ n,
      ((solver_to_lp solver).formulation n).num_constraints ≤
        p.eval (solver.time_bound.eval n)

-- ════════════════════════════════════════════════════════════
-- Section 4: (removed: poly_lp_induces_bounded_selector was a constant-false selector placeholder)
-- ════════════════════════════════════════════════════════════

-- (Removed: poly_lp_induces_bounded_selector was a constant-false selector placeholder.
-- For a correct selector, use poly_lp_implies_poly_selector below.)

-- ════════════════════════════════════════════════════════════
-- Section 5: Theorem 1 — lp_size_bounds_nonneg_rank (geometric lane)
-- ════════════════════════════════════════════════════════════

/-- Core geometric theorem: a poly-size LP formulation implies poly-bounded
    nonneg rank of the correlation polytope's slack matrix (via Yannakakis).

    This is the GEOMETRIC lane of Chain 6. It does not require PolyTimeImpliesPolyLP
    or any computational hypothesis.

    Hypotheses:
    - lp_solver: a poly-size LP family
    - polytopes: correlation polytopes for the family
    - yt: Yannakakis theorem for each correlation polytope (carried structure)
    - h_ef: the LP at size n is an extended formulation of the correlation polytope
    - h_facets_le: the LP's number of constraints bounds the extended formulation's facets

    Conclusion: nonneg rank of the slack matrix is at most size_bound.eval n.

    Note: h_ef and h_facets_le are explicit because the connection between an LP
    formulation (in the computational sense) and an extended formulation (in the
    geometric sense) is the substantive claim of the chain — it should not be hidden. -/
theorem lp_size_bounds_nonneg_rank
    (family : SATFamily)
    (lp_solver : PolyLPSolver family)
    (polytopes : SATFamilyPolytope family)
    (yt : ∀ n, YannakakisTheorem (polytopes.polytopes n).polytope)
    (h_ef : ∀ n, ExtendedFormulation (polytopes.polytopes n).polytope)
    (h_facets_le : ∀ n, (h_ef n).Q.num_facets ≤ lp_solver.size_bound.eval n)
    (n : Nat) :
    hasNonnegRankAtMost
      (slackMatrix (polytopes.polytopes n).polytope)
      (lp_solver.size_bound.eval n) := by
  obtain ⟨r, hr_le, h_nonempty⟩ := (yt n).ext_to_rank (h_ef n)
  exact ⟨r, Nat.le_trans hr_le (h_facets_le n), h_nonempty⟩

-- ════════════════════════════════════════════════════════════
-- Section 6: Theorem 2 — no_poly_lp_from_hard_instances (geometric lock)
-- ════════════════════════════════════════════════════════════

/-- Geometric lock: superpolynomial nonneg rank implies no poly-size LP.

    This is the CORE geometric lock of Chain 6. It starts from the geometric
    assumption (poly-size LP → low nonneg rank) and derives a contradiction
    when the instances are geometrically hard (superpolynomial nonneg rank).

    Assumptions:
    - GeometricFaithful gf: a hard family (superpolynomial nonneg rank)
    - h_ef: LP formulations are extended formulations of the correlation polytopes
    - h_facets_le: LP constraint count bounds extended formulation facets

    Conclusion: no poly-size LP exists for the family.

    DESIGN: This theorem does NOT mention poly-time SAT solvers.
    That is the correct factorization: geometry first, computation as corollary. -/
theorem no_poly_lp_from_hard_instances
    (family : SATFamily)
    (gf : GeometricFaithful family)
    -- h_ef_bounded: for any LP solver, a extended-formulation witness exists at each n
    -- such that the facet count is bounded by the LP's polynomial bound.
    -- This bundles the extended-formulation existence and its size bound together,
    -- since both depend on the LP solver (the LP IS the extended formulation).
    (h_ef_bounded : ∀ (lp_solver : PolyLPSolver family) (n : Nat),
      ∃ (ef : ExtendedFormulation (gf.polytopes.polytopes n).polytope),
        ef.Q.num_facets ≤ lp_solver.size_bound.eval n) :
    ¬Nonempty (PolyLPSolver family) := by
  intro ⟨lp_solver⟩
  obtain ⟨n, h_not_rank⟩ := gf.h_hard_family lp_solver.size_bound
  apply h_not_rank
  obtain ⟨ef, h_facets_le⟩ := h_ef_bounded lp_solver n
  obtain ⟨r, hr_le, h_nonempty⟩ := (gf.yannakakis n).ext_to_rank ef
  exact ⟨r, Nat.le_trans hr_le h_facets_le, h_nonempty⟩

-- ════════════════════════════════════════════════════════════
-- Section 7: Theorem 3 — poly_lp_implies_poly_selector
-- ════════════════════════════════════════════════════════════

/-- A poly-size LP solver with poly-bounded variable count implies a correct
    poly-bounded selector family.

    When the number of SAT variables is at most the LP capacity bound, the LP
    solver induces a correct BoundedSelector that exactly captures satisfiability.

    Proof: accessed_vars = all variables (length = num_vars ≤ capacity).
    select = instanceSatisfied. h_factors: agree on all vars → same result. -/
theorem poly_lp_implies_poly_selector
    (family : SATFamily)
    (lp_solver : PolyLPSolver family)
    (h_var_bound : ∀ n, (family n).num_vars ≤ lp_solver.size_bound.eval n)
    (n : Nat) :
    ∃ (sel : BoundedSelector (family n) (lp_solver.size_bound.eval n)),
      ∀ a, sel.select a = (family n).instanceSatisfied a := by
  classical
  haveI : Fintype (family n).Assignment := by
    show Fintype (Fin (family n).num_vars → Bool); exact inferInstance
  refine ⟨{
    select := fun a => (family n).instanceSatisfied a
    accessed_vars := Finset.univ.val.toList
    h_bounded := by
      simp [Finset.card_univ]
      exact h_var_bound n
    h_factors := by
      intro a₁ a₂ h_agree
      congr 1; funext v
      apply h_agree v
      simp [Finset.mem_val, Finset.mem_univ]
  }, fun a => rfl⟩

-- ════════════════════════════════════════════════════════════
-- Section 8: Def 2 — poly_lp_induces_lp_bounded_selector
-- ════════════════════════════════════════════════════════════

/-- When variable count ≤ LP capacity, a poly-LP solver induces a correct
    LP-bounded selector, combining both structural and correctness properties. -/
noncomputable def poly_lp_induces_lp_bounded_selector
    (family : SATFamily)
    (lp_solver : PolyLPSolver family)
    (h_var_bound : ∀ n, (family n).num_vars ≤ lp_solver.size_bound.eval n)
    (n : Nat) :
    LPBoundedSelector (family n) (lp_solver.size_bound.eval n) :=
  let h := poly_lp_implies_poly_selector family lp_solver h_var_bound n
  { lp := lp_solver.formulation n
    h_bounded := lp_solver.h_poly_size n
    selector := Classical.choose h
    h_correct := Classical.choose_spec h }

-- ════════════════════════════════════════════════════════════
-- Section 9: Theorem 4 — geometric_chain_no_poly_solver (computational corollary)
-- ════════════════════════════════════════════════════════════

/-- Optional computational corollary: superpolynomial nonneg rank implies no poly-time solver.

    This is NOT the core geometric lock. It is an additional step that requires
    the open hypothesis PolyTimeImpliesPolyLP (poly-time solving implies poly-size LP).

    Chain of reasoning:
      GeometricFaithful (hard instances) → no poly-size LP [no_poly_lp_from_hard_instances]
      PolyTimeImpliesPolyLP → poly-time solver would yield poly-size LP
      Contradiction.

    The hypothesis PolyTimeImpliesPolyLP is extremely strong and related to P vs NP.
    It is explicitly marked as open and made an explicit parameter here. -/
theorem geometric_chain_no_poly_solver
    (family : SATFamily)
    (gf : GeometricFaithful family)
    (h_ef_bounded : ∀ (lp_solver : PolyLPSolver family) (n : Nat),
      ∃ (ef : ExtendedFormulation (gf.polytopes.polytopes n).polytope),
        ef.Q.num_facets ≤ lp_solver.size_bound.eval n)
    (h_poly_time_implies_lp : PolyTimeImpliesPolyLP family) :
    ¬Nonempty (PolyTimeSolver family) := by
  intro ⟨solver⟩
  -- poly-time solver → poly-size LP (via open hypothesis h_poly_time_implies_lp)
  -- → contradiction with GeometricFaithful (no poly LP for hard instances)
  have h_no_lp := no_poly_lp_from_hard_instances family gf h_ef_bounded
  exact h_no_lp ⟨h_poly_time_implies_lp.solver_to_lp solver⟩

end ClassicalConstraints
