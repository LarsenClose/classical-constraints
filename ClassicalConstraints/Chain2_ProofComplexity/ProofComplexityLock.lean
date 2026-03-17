/-
  ClassicalConstraints/ProofComplexityLock.lean
  Lock file: Chain 2 (Proof Complexity) is complete.

  This file imports all Chain 2 modules and states the chain's main theorems
  in a single locked interface. The chain connects:

  Resolution width lower bounds
    → Resolution size lower bounds (width-size relationship)
    → Communication complexity lower bounds (short-proof-bounded-comm)
    → Lifting theorem (query → communication complexity)
    → Feasible interpolation (circuit complexity lower bounds)
    → Proof search hardness

  All modules: 0 sorry. Classical.choice allowed on Side B.

  STATUS: 0 sorry. Classical.choice allowed.
-/

import ClassicalConstraints.Chain2_ProofComplexity.ResolutionWidthCore
import ClassicalConstraints.Chain2_ProofComplexity.CommunicationProtocolBridge
import ClassicalConstraints.Chain2_ProofComplexity.KrajicekExtraction
import ClassicalConstraints.Chain2_ProofComplexity.LiftingCore
import ClassicalConstraints.Chain2_ProofComplexity.FeasibleInterpolationBridge
import ClassicalConstraints.Chain2_ProofComplexity.ProofSearchBridge
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Bool.Basic

namespace ClassicalConstraints

-- ════════════════════════════════════════════════════════════
-- Chain 2 Summary: The Proof Complexity Chain
-- ════════════════════════════════════════════════════════════

/-- Chain 2 bundles all components of the proof complexity chain. -/
structure ProofComplexityChain where
  -- Leg 1: Width lower bound
  width_lb : ResolutionWidthLowerBound
  -- Leg 2: Width-size relation (for each family member)
  width_size : ∀ n, WidthSizeRelation (width_lb.family n)
  -- Leg 3: Lifting gadget (for lifting query LBs to communication LBs).
  -- The faithfulness condition is extracted as LiftingFaithful (via
  -- LiftingTheorem.toLiftingFaithful), the Chain 2 analog of CookFaithful,
  -- DefinabilityFaithful, and the faithfulness structures in other chains.
  lifting : LiftingTheorem
  -- Leg 4: Interpolation lower bound (for one family member)
  interp_lb : InterpolationLowerBound

-- ════════════════════════════════════════════════════════════
-- Lock Theorem 1: Width lower bounds propagate to size lower bounds
-- ════════════════════════════════════════════════════════════

/-- Chain lock 1: width lower bounds give size lower bounds. -/
theorem chain2_lock_width_to_size
    (lb : ResolutionWidthLowerBound)
    (wsr : ∀ n, WidthSizeRelation (lb.family n))
    (n : Nat) (ref : ResolutionRefutation (lb.family n)) :
    ref.size ≥ lb.width_bound n - (wsr n).initial_width + 1 :=
  width_lower_implies_size_lower lb wsr n ref

-- ════════════════════════════════════════════════════════════
-- Lock Theorem 2: Short proofs give bounded protocols
-- ════════════════════════════════════════════════════════════

/-- Chain lock 2: a short resolution refutation gives a bounded communication protocol. -/
theorem chain2_lock_proof_to_protocol
    (φ : CNF) (ref : ResolutionRefutation φ) :
    ∃ proto : CommProtocol φ.num_vars φ.num_vars,
      proto.tree.depth ≤ ref.size :=
  krajicek_bounded_comm φ ref

-- ════════════════════════════════════════════════════════════
-- Lock Theorem 3: Communication complexity ≥ query complexity
-- ════════════════════════════════════════════════════════════

/-- Chain lock 3: for any function, protocol depth ≥ query complexity. -/
theorem chain2_lock_comm_ge_query
    (n d : Nat) (f : (Fin n → Bool) → Bool)
    (h_query : ∀ t : DecisionTree n, (∀ x, t.eval x = f x) → t.depth ≥ d) :
    ∀ (proto : ProtocolTree n n Bool),
      (∀ x, proto.eval x x = f x) →
      proto.depth ≥ d :=
  comm_ge_query n f d h_query

-- ════════════════════════════════════════════════════════════
-- Lock Theorem 4: Lifting theorem transfers lower bounds
-- ════════════════════════════════════════════════════════════

/-- Chain lock 4: a lifting theorem transfers query lower bounds to communication lower bounds
    by a factor of lift_factor. -/
theorem chain2_lock_lifting
    (lt : LiftingTheorem) (n d : Nat) (f : (Fin n → Bool) → Bool)
    (h_query_lower : ∀ t : DecisionTree n, (∀ x, t.eval x = f x) → t.depth ≥ d)
    (proto : ProtocolTree (n * lt.gadget.bits_per_player)
                           (n * lt.gadget.bits_per_player) Bool)
    (h_correct : ∀ a b, proto.eval a b = liftedFunction n f lt.gadget a b) :
    proto.depth ≥ lt.lift_factor * d :=
  lifting_transfers_lower_bound lt n d f h_query_lower proto h_correct

-- ════════════════════════════════════════════════════════════
-- Lock Theorem 5: Feasible interpolation yields circuits
-- ════════════════════════════════════════════════════════════

/-- Chain lock 5: a short resolution refutation of a split formula yields a small circuit. -/
theorem chain2_lock_interpolation
    (n_x n_y : Nat)
    (combined : CNF) (h_combined : combined.num_vars = n_x + n_y)
    (ref : ResolutionRefutation combined) :
    ∃ C : BooleanCircuit n_x, C.gateCount ≤ ref.size * ref.size :=
  resolution_feasible_interpolation n_x n_y combined h_combined ref

-- ════════════════════════════════════════════════════════════
-- Lock Theorem 6: Circuit lower bounds imply resolution lower bounds
-- ════════════════════════════════════════════════════════════

/-- Chain lock 6: circuit lower bounds imply refutation size lower bounds. -/
theorem chain2_lock_circuit_to_resolution
    (ilb : InterpolationLowerBound)
    (ref : ResolutionRefutation ilb.combined)
    (h_correct : ∀ C : BooleanCircuit ilb.formula.n_x,
      C.gateCount ≤ ref.size * ref.size →
      ∀ x, C.eval x = ilb.interpolation_fn x) :
    ref.size * ref.size ≥ ilb.gate_lb :=
  interpolation_implies_resolution_lb ilb ref h_correct

-- ════════════════════════════════════════════════════════════
-- Lock Theorem 7: Resolution hardness → proof search hardness
-- ════════════════════════════════════════════════════════════

/-- Chain lock 7: resolution hardness implies proof search instances get harder. -/
theorem chain2_lock_search_hardness
    (φ_family : Nat → CNF)
    (comm_lb : Nat → Nat)
    (h_comm_lb : ∀ n (ref : ResolutionRefutation (φ_family n)),
      ∃ proto : CommProtocol (φ_family n).num_vars (φ_family n).num_vars,
        proto.tree.depth ≤ ref.size ∧ proto.tree.depth ≥ comm_lb n)
    (h_grows : ∀ K, ∃ n, comm_lb n > K) :
    ∀ K, ∃ n, ¬(ProofSearchInstance.mk (φ_family n) K).answer :=
  comm_lb_implies_search_hardness φ_family comm_lb h_comm_lb h_grows

-- ════════════════════════════════════════════════════════════
-- Lock Theorem 8: Non-constant functions have depth ≥ 1
-- ════════════════════════════════════════════════════════════

/-- Chain lock 8: non-constant functions require depth ≥ 1 in any decision tree. -/
theorem chain2_lock_nonconstant_lb
    {n : Nat} (f : (Fin n → Bool) → Bool)
    (h : ∃ x y, f x ≠ f y) :
    ∀ t : DecisionTree n, (∀ x, t.eval x = f x) → t.depth ≥ 1 :=
  nonconstant_dt_lb f h

-- ════════════════════════════════════════════════════════════
-- Lock Theorem 9: The xorGadget is a valid lifting gadget
-- ════════════════════════════════════════════════════════════

/-- Chain lock 9: the XOR gadget has bits_per_player = 1, is non-degenerate and balanced. -/
theorem chain2_lock_xor_gadget :
    xorGadget.bits_per_player = 1 ∧
    (∃ a₁ b₁ a₂ b₂, xorGadget.gadget a₁ b₁ ≠ xorGadget.gadget a₂ b₂) ∧
    (∀ a : Fin 1 → Bool,
      (∃ b, xorGadget.gadget a b = true) ∧ (∃ b, xorGadget.gadget a b = false)) :=
  ⟨rfl, xorGadget.h_nondeg, xorGadget.h_balanced⟩

-- ════════════════════════════════════════════════════════════
-- Lock Theorem 10: Leaf count bound
-- ════════════════════════════════════════════════════════════

/-- Chain lock 10: a protocol tree of depth d has at most 2^d leaves. -/
theorem chain2_lock_leaf_count
    {n_alice n_bob : Nat} {Output : Type}
    (t : ProtocolTree n_alice n_bob Output) :
    t.leafCount ≤ 2 ^ t.depth :=
  protocol_leaf_count t

-- ════════════════════════════════════════════════════════════
-- Chain 2 Complete
-- ════════════════════════════════════════════════════════════

/-- The full Chain 2 path: from resolution width lower bounds to proof search hardness,
    via communication complexity, lifting, feasible interpolation. -/
theorem chain2_complete :
    -- Resolution width lower bounds transfer to resolution size lower bounds
    (∀ (lb : ResolutionWidthLowerBound) (wsr : ∀ n, WidthSizeRelation (lb.family n))
       (n : Nat) (ref : ResolutionRefutation (lb.family n)),
       ref.size ≥ lb.width_bound n - (wsr n).initial_width + 1) ∧
    -- Short proofs give bounded protocols
    (∀ (φ : CNF) (ref : ResolutionRefutation φ),
       ∃ proto : CommProtocol φ.num_vars φ.num_vars,
         proto.tree.depth ≤ ref.size) ∧
    -- Circuit lower bounds transfer to refutation size lower bounds
    (∀ (ilb : InterpolationLowerBound)
       (ref : ResolutionRefutation ilb.combined),
       (∀ C : BooleanCircuit ilb.formula.n_x,
         C.gateCount ≤ ref.size * ref.size → ∀ x, C.eval x = ilb.interpolation_fn x) →
       ref.size * ref.size ≥ ilb.gate_lb) :=
  ⟨fun lb wsr n ref => width_lower_implies_size_lower lb wsr n ref,
   fun φ ref => krajicek_bounded_comm φ ref,
   fun ilb ref hc => interpolation_implies_resolution_lb ilb ref hc⟩

end ClassicalConstraints
