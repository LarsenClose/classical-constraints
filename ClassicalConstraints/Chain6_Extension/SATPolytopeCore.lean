/-
  ClassicalConstraints/SATPolytopeCore.lean
  SAT instances as polytopes: correlation polytopes, LP formulations,
  and the connection to nonneg rank via Yannakakis.

  Classical.choice is allowed (Side B).
  No sorry.
-/

import ClassicalConstraints.Chain6_Extension.SlackMatrixCore
import ClassicalConstraints.Shared.SATPresheafCore
import ClassicalConstraints.Shared.CookSelectorBridge

namespace ClassicalConstraints

open SATInstance

-- ════════════════════════════════════════════════════════════
-- Section 1: 0/1 assignment embedding
-- ════════════════════════════════════════════════════════════

/-- A 0/1 assignment viewed as a real vector. -/
def assignmentToReal {n : Nat} (a : Fin n → Bool) : Fin n → ℝ :=
  fun i => if a i then 1 else 0

/-- assignmentToReal maps to {0, 1}: every coordinate is 0 or 1. -/
theorem assignmentToReal_01 {n : Nat} (a : Fin n → Bool) (i : Fin n) :
    assignmentToReal a i = 0 ∨ assignmentToReal a i = 1 := by
  unfold assignmentToReal
  split_ifs with h
  · right; rfl
  · left; rfl

-- ════════════════════════════════════════════════════════════
-- Section 2: CorrelationPolytope
-- ════════════════════════════════════════════════════════════

/-- The correlation polytope for a SAT instance: the set of satisfying
    assignments embedded as 0/1 points in R^n.

    For unsatisfiable instances, this is the empty set (no vertices).
    We only define it for satisfiable instances with at least one
    satisfying assignment. -/
structure CorrelationPolytope (phi : SATInstance) where
  /-- The polytope in R^(num_vars). -/
  polytope : Polytope phi.num_vars
  /-- Each vertex corresponds to a satisfying assignment. -/
  h_vertices_satisfy : ∀ (v : Fin polytope.num_vertices),
    ∃ (a : phi.Assignment),
      phi.instanceSatisfied a = true ∧
      polytope.vertices v = assignmentToReal a
  /-- Every satisfying assignment appears as a vertex. -/
  h_complete : ∀ (a : phi.Assignment),
    phi.instanceSatisfied a = true →
    ∃ (v : Fin polytope.num_vertices),
      polytope.vertices v = assignmentToReal a

-- ════════════════════════════════════════════════════════════
-- Section 3: SATFamilyPolytope
-- ════════════════════════════════════════════════════════════

/-- A family of correlation polytopes, one for each instance in a SAT family. -/
structure SATFamilyPolytope (family : SATFamily) where
  /-- For each size n, the correlation polytope of the instance. -/
  polytopes : (n : Nat) → CorrelationPolytope (family n)

-- ════════════════════════════════════════════════════════════
-- Section 4: LP formulation
-- ════════════════════════════════════════════════════════════

/-- An LP formulation of a SAT instance: a polytope whose 0/1 vertices
    correspond exactly to satisfying assignments.

    The size of the LP (number of constraints) is the key measure.
    A "poly-size LP" has at most poly(n) constraints. -/
structure LPFormulation (phi : SATInstance) where
  /-- Number of additional (auxiliary) variables. -/
  num_aux : Nat
  /-- The LP polytope (in R^(num_vars + num_aux)). -/
  lp_polytope : Polytope (phi.num_vars + num_aux)
  /-- Number of constraints in the LP. -/
  num_constraints : Nat
  /-- The LP polytope has at most num_constraints facets. -/
  h_size : lp_polytope.num_facets ≤ num_constraints
  /-- Projection correctness: the LP's feasible 0/1 points project
      to exactly the satisfying assignments. -/
  h_correct_forward : ∀ (a : phi.Assignment),
    phi.instanceSatisfied a = true →
    ∃ (w : Fin lp_polytope.num_vertices),
      ∀ (j : Fin phi.num_vars),
        lp_polytope.vertices w (Fin.castAdd num_aux j) = assignmentToReal a j
  h_correct_backward : ∀ (w : Fin lp_polytope.num_vertices),
    (∀ (j : Fin phi.num_vars),
      lp_polytope.vertices w (Fin.castAdd num_aux j) = 0 ∨
      lp_polytope.vertices w (Fin.castAdd num_aux j) = 1) →
    ∃ (a : phi.Assignment),
      phi.instanceSatisfied a = true ∧
      ∀ (j : Fin phi.num_vars),
        lp_polytope.vertices w (Fin.castAdd num_aux j) = assignmentToReal a j

-- ════════════════════════════════════════════════════════════
-- Section 5: PolyLPSolver
-- ════════════════════════════════════════════════════════════

/-- A polynomial-size LP formulation for a SAT family:
    for each size n, an LP with at most poly(n) constraints. -/
structure PolyLPSolver (family : SATFamily) where
  /-- The LP formulation at each size. -/
  formulation : (n : Nat) → LPFormulation (family n)
  /-- Polynomial bound on LP size. -/
  size_bound : PolyBound
  /-- The LP size is bounded polynomially. -/
  h_poly_size : ∀ n, (formulation n).num_constraints ≤ size_bound.eval n

-- ════════════════════════════════════════════════════════════
-- Section 6: Theorem 1 — LP implies low nonneg rank
-- ════════════════════════════════════════════════════════════

/-- A poly-size LP formulation implies the correlation polytope's slack
    matrix has polynomially bounded nonneg rank via Yannakakis. -/
theorem lp_implies_low_nonneg_rank {phi : SATInstance}
    (cp : CorrelationPolytope phi)
    (yt : YannakakisTheorem cp.polytope)
    (lp : LPFormulation phi)
    (h_ef : ExtendedFormulation cp.polytope)
    (h_facets_le : h_ef.Q.num_facets ≤ lp.num_constraints) :
    hasNonnegRankAtMost (slackMatrix cp.polytope) lp.num_constraints := by
  -- Use Yannakakis forward direction: extended formulation → nonneg rank bound.
  obtain ⟨r, hr_le, h_nonempty⟩ := yt.ext_to_rank h_ef
  exact ⟨r, Nat.le_trans hr_le h_facets_le, h_nonempty⟩

/-- Direct application of Yannakakis forward direction:
    an extended formulation of P with r facets implies nonneg rank ≤ r. -/
theorem lp_as_extended_formulation_bounds_rank {phi : SATInstance}
    (cp : CorrelationPolytope phi)
    (yt : YannakakisTheorem cp.polytope)
    (h_ef : ExtendedFormulation cp.polytope) :
    hasNonnegRankAtMost (slackMatrix cp.polytope) h_ef.Q.num_facets :=
  yt.ext_to_rank h_ef

-- ════════════════════════════════════════════════════════════
-- Section 7: Theorem 2 — Vertices of correlation polytope are 0/1
-- ════════════════════════════════════════════════════════════

/-- Vertices of the correlation polytope are 0/1 vectors. -/
theorem correlation_polytope_vertices_01 {phi : SATInstance}
    (cp : CorrelationPolytope phi) :
    ∀ (v : Fin cp.polytope.num_vertices) (j : Fin phi.num_vars),
      cp.polytope.vertices v j = 0 ∨ cp.polytope.vertices v j = 1 := by
  intro v j
  obtain ⟨a, _, h_eq⟩ := cp.h_vertices_satisfy v
  rw [show cp.polytope.vertices v = assignmentToReal a from h_eq]
  exact assignmentToReal_01 a j

-- ════════════════════════════════════════════════════════════
-- Section 8: Theorem 3 — Vertex count and satisfying assignments
-- ════════════════════════════════════════════════════════════

/-- The number of vertices of the correlation polytope equals the number
    of satisfying assignments, given injectivity of the vertex-to-point map. -/
theorem vertex_count_matches_solutions {phi : SATInstance}
    (cp : CorrelationPolytope phi)
    (h_inj : Function.Injective (fun v => cp.polytope.vertices v))
    [hfin : Fintype phi.Assignment] :
    cp.polytope.num_vertices =
      (Finset.univ.filter (fun a : phi.Assignment => phi.instanceSatisfied a = true)).card := by
  classical
  -- Rewrite num_vertices as a Finset cardinality.
  conv_lhs => rw [show cp.polytope.num_vertices =
    (Finset.univ : Finset (Fin cp.polytope.num_vertices)).card from by
      simp [Finset.card_univ]]
  apply Nat.le_antisymm
  · -- Map v ↦ the satisfying assignment at v (by h_vertices_satisfy).
    apply Finset.card_le_card_of_injOn
      (fun v : Fin cp.polytope.num_vertices => Classical.choose (cp.h_vertices_satisfy v))
    · -- Maps into the filter: a_v is satisfying.
      intro v _
      rw [Finset.mem_coe, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (Classical.choose_spec (cp.h_vertices_satisfy v)).1⟩
    · -- Injective: a_v = a_w → v = w via h_inj.
      intro v _ w _ h_eq
      simp only at h_eq
      apply h_inj
      have hv := (Classical.choose_spec (cp.h_vertices_satisfy v)).2
      have hw := (Classical.choose_spec (cp.h_vertices_satisfy w)).2
      show cp.polytope.vertices v = cp.polytope.vertices w
      rw [hv, hw, h_eq]
  · -- Map a ↦ the vertex index for assignment a (by h_complete).
    -- For this direction, define the vertex-finding function on the filter subtype.
    -- Use fun a ha => Classical.choose (h_complete a (ha from filter membership)).
    -- Finset.card_le_card_of_injOn takes f : α → β with MapsTo and InjOn.
    -- We pass a function that gets the vertex for each satisfying assignment.
    -- The membership proof comes from the InjOn goals (ha, hb).
    -- We need to be careful: the function is defined on ALL assignments,
    -- but the proof it works on satisfying ones comes from ha.
    -- Use Classical.choice to extract the vertex unconditionally.
    apply Finset.card_le_card_of_injOn
      (fun a : phi.Assignment =>
        if h : phi.instanceSatisfied a = true
        then Classical.choose (cp.h_complete a h)
        else ⟨0, cp.polytope.h_vertices_nonempty⟩)
    · intro a ha
      rw [Finset.mem_coe]; exact Finset.mem_univ _
    · intro a ha b hb h_eq
      simp only at h_eq
      rw [Finset.mem_coe, Finset.mem_filter] at ha hb
      have ha_sat : phi.instanceSatisfied a = true := ha.2
      have hb_sat : phi.instanceSatisfied b = true := hb.2
      simp only [ha_sat, hb_sat, dite_true] at h_eq
      have hva := (Classical.choose_spec (cp.h_complete a ha_sat))
      have hvb := (Classical.choose_spec (cp.h_complete b hb_sat))
      -- h_eq : vertex for a = vertex for b
      -- hva : vertices (v_a) = assignmentToReal a
      -- hvb : vertices (v_b) = assignmentToReal b
      -- h_eq says v_a = v_b, so assignmentToReal a = assignmentToReal b.
      have h_pt : assignmentToReal a = assignmentToReal b := by
        rw [← hva, ← hvb, h_eq]
      funext i
      have := congr_fun h_pt i
      simp only [assignmentToReal] at this
      split_ifs at this with ha_i hb_i
      · rw [ha_i, hb_i]
      · linarith
      · linarith
      · -- both false: a i = false = b i
        cases ha : a i <;> cases hb : b i <;> simp_all

-- ════════════════════════════════════════════════════════════
-- Section 9: LP formulation gives an extended formulation
-- ════════════════════════════════════════════════════════════

/-- An LP formulation of a SAT instance gives an extended formulation of the
    correlation polytope when the LP polytope projects to the correlation polytope.

    This is the key connection: LP size = extension complexity. -/
def lp_gives_extended_formulation {phi : SATInstance}
    (cp : CorrelationPolytope phi)
    (lp : LPFormulation phi)
    (h_proj_complete : ∀ (v : Fin cp.polytope.num_vertices),
      ∃ (w : Fin lp.lp_polytope.num_vertices),
        ∀ (j : Fin phi.num_vars),
          cp.polytope.vertices v j =
            lp.lp_polytope.vertices w (Fin.castAdd lp.num_aux j)) :
    ExtendedFormulation cp.polytope where
  num_aux := lp.num_aux
  Q := lp.lp_polytope
  h_proj := h_proj_complete

end ClassicalConstraints
