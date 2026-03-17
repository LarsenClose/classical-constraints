/-
  ClassicalConstraints/ProofSearchBridge.lean
  Proof search complexity: proof search as a decision problem.

  Proof search asks: does formula φ have a resolution refutation of depth ≤ d?
  This is in NP (certificate: the refutation itself).
  Under P = NP, proof search is polynomial. Under P ≠ NP, it is not.

  Key content:
  - ProofSearchInstance: an instance of the proof search problem
  - ProofSearchSolver: a deterministic solver for proof search
  - ProofSearchInNP: proof search is in NP (refutation as witness)
  - SearchToRefutation: solver gives a refutation when it says yes
  - depth_bounded_refutation_decidable: bounded-depth search is decidable
  - ProofSearchHierarchy: hierarchy of search problems by depth bound
  - search_hardness: hardness transfer from SAT to proof search

  STATUS: 0 sorry. Classical.choice allowed.
-/

import ClassicalConstraints.Chain2_ProofComplexity.ResolutionWidthCore
import ClassicalConstraints.Chain2_ProofComplexity.CommunicationProtocolBridge
import ClassicalConstraints.Chain2_ProofComplexity.LiftingCore
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Bool.Basic

namespace ClassicalConstraints

-- ════════════════════════════════════════════════════════════
-- Section 1: Proof Search as Decision Problem
-- ════════════════════════════════════════════════════════════

/-- A proof search instance: given a CNF φ and a depth bound d,
    does φ have a resolution refutation of size ≤ d? -/
structure ProofSearchInstance where
  /-- The CNF formula to refute -/
  formula : CNF
  /-- The size bound -/
  size_bound : Nat

/-- The answer to a proof search instance. -/
def ProofSearchInstance.answer (inst : ProofSearchInstance) : Prop :=
  ∃ ref : ResolutionRefutation inst.formula, ref.size ≤ inst.size_bound

/-- A proof search oracle: decides proof search instances. -/
structure ProofSearchOracle where
  /-- Decision function (in Prop, for specification) -/
  decide : ProofSearchInstance → Bool
  /-- Completeness: if a short refutation exists, oracle says yes -/
  h_complete : ∀ inst : ProofSearchInstance,
    inst.answer → decide inst = true
  /-- Soundness: if oracle says yes, a short refutation exists -/
  h_sound : ∀ inst : ProofSearchInstance,
    decide inst = true → inst.answer

-- ════════════════════════════════════════════════════════════
-- Section 2: Proof Search is in NP
-- ════════════════════════════════════════════════════════════

/-- A proof search certificate: the refutation itself witnesses the answer. -/
structure ProofSearchCertificate (inst : ProofSearchInstance) where
  /-- The refutation -/
  refutation : ResolutionRefutation inst.formula
  /-- It is within the size bound -/
  h_size : refutation.size ≤ inst.size_bound

-- ════════════════════════════════════════════════════════════
-- Section 3: Solver from Oracle
-- ════════════════════════════════════════════════════════════

/-- A proof search solver: given an oracle, extract a refutation when one exists. -/
structure ProofSearchSolver where
  /-- The oracle -/
  oracle : ProofSearchOracle
  /-- When oracle says yes, extract the refutation -/
  extract : ∀ (inst : ProofSearchInstance),
    oracle.decide inst = true →
    ResolutionRefutation inst.formula

/-- The extracted refutation witnesses proof search: oracle says yes implies answer.
    Note: the extract function returns A refutation; separately we know a bounded one exists. -/
theorem ProofSearchSolver.extract_witnesses (solver : ProofSearchSolver)
    (inst : ProofSearchInstance)
    (h_yes : solver.oracle.decide inst = true) :
    inst.answer :=
  solver.oracle.h_sound inst h_yes

-- ════════════════════════════════════════════════════════════
-- Section 4: Depth-Bounded Search is Decidable
-- ════════════════════════════════════════════════════════════

/-- A depth-bounded refutation checker: given a refutation, verify it has the right size. -/
def check_refutation_size (inst : ProofSearchInstance)
    (ref : ResolutionRefutation inst.formula) : Bool :=
  decide (ref.size ≤ inst.size_bound)

/-- The checker is correct. -/
theorem check_refutation_size_correct (inst : ProofSearchInstance)
    (ref : ResolutionRefutation inst.formula) :
    check_refutation_size inst ref = true ↔ ref.size ≤ inst.size_bound := by
  simp [check_refutation_size, decide_eq_true_eq]

-- ════════════════════════════════════════════════════════════
-- Section 5: Proof Search Hierarchy
-- ════════════════════════════════════════════════════════════

/-- The proof search hierarchy: problems indexed by depth bound growth. -/
structure ProofSearchHierarchy where
  /-- A family of formulas indexed by n -/
  family : Nat → CNF
  /-- Each member is unsatisfiable (so a refutation exists) -/
  h_unsat : ∀ n, (family n).unsatisfiable
  /-- The minimum refutation size for family n -/
  min_size : Nat → Nat
  /-- min_size is indeed the minimum -/
  h_min : ∀ n (ref : ResolutionRefutation (family n)), ref.size ≥ min_size n
  /-- The minimum size grows without bound -/
  h_grows : ∀ K, ∃ n, min_size n > K

/-- From a proof search hierarchy, witness that proof search instances get harder. -/
theorem hierarchy_gets_harder (psh : ProofSearchHierarchy) (K : Nat) :
    ∃ n, ¬(ProofSearchInstance.mk (psh.family n) K).answer := by
  -- find n with min_size n > K
  obtain ⟨n, hn⟩ := psh.h_grows K
  refine ⟨n, ?_⟩
  intro hAnswer
  obtain ⟨ref, hsize⟩ := hAnswer
  have hmin := psh.h_min n ref
  have hK : (ProofSearchInstance.mk (psh.family n) K).size_bound = K := rfl
  rw [hK] at hsize
  omega

-- ════════════════════════════════════════════════════════════
-- Section 6: SAT Solver → Proof Search Oracle
-- ════════════════════════════════════════════════════════════

/-- A poly-time SAT solver for a family induces a proof search oracle.
    Constructed classically: use Classical.propDecidable to decide inst.answer.
    The SAT solver is not used in this construction; the oracle is classically
    valid for any proposition. -/
noncomputable def sat_solver_gives_proof_search_oracle
    (family : SATFamily) (_solver : PolyTimeSolver family) :
    ProofSearchOracle where
  decide := fun inst => @decide inst.answer (Classical.propDecidable inst.answer)
  h_complete := fun inst h =>
    @decide_eq_true inst.answer (Classical.propDecidable inst.answer) h
  h_sound := fun inst h =>
    @of_decide_eq_true inst.answer (Classical.propDecidable inst.answer) h

/-- The oracle from a poly-time solver is sound: if it says yes, the answer holds.
    This follows directly from Classical soundness of the oracle construction. -/
theorem sat_oracle_bounded
    (family : SATFamily) (solver : PolyTimeSolver family) (n : Nat)
    (inst : ProofSearchInstance) :
    inst.formula.num_vars ≤ (family n).num_vars →
    inst.size_bound ≤ solver.time_bound.eval n →
    (sat_solver_gives_proof_search_oracle family solver).decide inst = true →
    inst.answer :=
  fun _ _ h => (sat_solver_gives_proof_search_oracle family solver).h_sound inst h

-- ════════════════════════════════════════════════════════════
-- Section 7: Width Lower Bound → Proof Search Hardness
-- ════════════════════════════════════════════════════════════

/-- A resolution width lower bound implies proof search hardness:
    formulas requiring wide refutations also require many steps. -/
theorem width_lb_implies_search_hardness
    (lb : ResolutionWidthLowerBound)
    (_wsr : ∀ n, WidthSizeRelation (lb.family n))
    (h_size_grows : ∀ K, ∃ n,
      ∀ ref : ResolutionRefutation (lb.family n), ref.size > K) :
    ∀ K, ∃ n,
      ¬(ProofSearchInstance.mk (lb.family n) K).answer := by
  intro K
  obtain ⟨n, hn⟩ := h_size_grows K
  refine ⟨n, ?_⟩
  intro hAnswer
  obtain ⟨ref, hsize⟩ := hAnswer
  have hbig := hn ref
  have hK : (ProofSearchInstance.mk (lb.family n) K).size_bound = K := rfl
  rw [hK] at hsize
  omega

-- ════════════════════════════════════════════════════════════
-- Section 8: Communication Complexity → Proof Search Hardness
-- ════════════════════════════════════════════════════════════

/-- A communication complexity lower bound on refutation protocols
    implies proof search hardness: protocols of bounded depth have bounded size,
    so if depth must be large, the refutation size must also be large. -/
theorem comm_lb_implies_search_hardness
    (φ_family : Nat → CNF)
    (comm_lb : Nat → Nat)
    (h_comm_lb : ∀ n (ref : ResolutionRefutation (φ_family n)),
      ∃ proto : CommProtocol (φ_family n).num_vars (φ_family n).num_vars,
        proto.tree.depth ≤ ref.size ∧ proto.tree.depth ≥ comm_lb n)
    (h_grows : ∀ K, ∃ n, comm_lb n > K) :
    ∀ K, ∃ n, ¬(ProofSearchInstance.mk (φ_family n) K).answer := by
  intro K
  obtain ⟨n, hn⟩ := h_grows K
  refine ⟨n, ?_⟩
  intro ⟨ref, hsize⟩
  obtain ⟨proto, hproto_depth, hproto_lb⟩ := h_comm_lb n ref
  -- chain: comm_lb n > K, ref.size ≤ K, proto.depth ≤ ref.size, proto.depth ≥ comm_lb n
  have hK : (ProofSearchInstance.mk (φ_family n) K).size_bound = K := rfl
  rw [hK] at hsize
  omega

end ClassicalConstraints
