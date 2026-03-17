/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

ClassicalConstraints/ProtocolWitnessFamilyLock.lean — Chain-7 lock.
Connects constructive side (selfApp_not_grade_bounded impossibility)
with classical side (five protocol regimes as one witness family).

STATUS: 0 sorry, Classical.choice allowed.
Mirror axioms from constructive side are explicitly documented.
-/

import ClassicalConstraints.Chain7_Protocol.DistributedWitnessCore
import ClassicalConstraints.Chain7_Protocol.CapabilityWitnessInstance
import ClassicalConstraints.Chain7_Protocol.ConsensusWitnessInstance
import ClassicalConstraints.Chain7_Protocol.ZKProjectionInstance
import ClassicalConstraints.Chain7_Protocol.CoherenceTransportMeasure
import ClassicalConstraints.Chain7_Protocol.ValueCollapseInstance
import ClassicalConstraints.Shared.CookSelectorBridge
import ClassicalConstraints.Shared.CookFaithfulness
import ClassicalConstraints.Shared.SideAMirror

namespace ClassicalConstraints

-- ════════════════════════════════════════════════════════════
-- Step 1: Mirror types from constructive side (pnp-integrated)
-- ════════════════════════════════════════════════════════════

-- GradedReflModel_Mirror, SelfAppUnbounded_Mirror imported from SATBoundaryLock.

-- ════════════════════════════════════════════════════════════
-- Step 2: Mirror constructive theorems as axioms
-- ════════════════════════════════════════════════════════════

-- sideA_bounded_selector_impossible is imported transitively via SATBoundaryLock → SideAMirror.
-- That axiom mirrors selfApp_not_grade_bounded from
-- pnp-integrated/PNP/Transport/TransportCollapseObstruction.lean
-- (also bounded_selector_impossible_with_output_bound in
-- pnp-integrated/PNP/Categorical/SelectionObstructionCore.lean).

-- ════════════════════════════════════════════════════════════
-- Step 3: ConsequenceFaithful + Transfer
-- ════════════════════════════════════════════════════════════

-- ConsequenceFaithful is defined in Shared/CookFaithfulness.lean.
-- It extends CookFaithful with h_consequence (model_depth ≤ d → sat_depth ≤ d).

/-- Transfer hypothesis: bridges protocol-level bounded selector to
    grade-bounded evaluator in the model. -/
structure ProtocolTransfer
    (M : GradedReflModel_Mirror)
    (family : SATFamily)
    (enc : CookEncoding)
    (cf : ConsequenceFaithful enc) where
  transfer : (n : Nat) → (d : Nat) →
    BoundedSelector (family n) d →
    { f : M.carrier → M.carrier //
      (∀ x, M.grade (f x) ≤ d) ∧
      (∀ x, M.grade x ≤ d → f x = M.selfApp x) }

-- consequenceFaithful_to_cookFaithful is in Shared/CookFaithfulness.lean.

-- ════════════════════════════════════════════════════════════
-- Step 4: The Lock Theorem
-- ════════════════════════════════════════════════════════════

/-- THE LOCK: conditional on ConsequenceFaithful + ProtocolTransfer,
    no poly-time SAT solver exists. Same conclusion as SATBoundaryLock
    and ProofComplexityLock, reached via the distributed witness route. -/
theorem no_bounded_protocol_shortcuts
    (M : GradedReflModel_Mirror)
    (hub : SelfAppUnbounded_Mirror M)
    (family : SATFamily)
    (enc : CookEncoding)
    (cf : ConsequenceFaithful enc)
    (tr : ProtocolTransfer M family enc cf)
    (solver : PolyTimeSolver family) :
    False := by
  let n := 1
  let d := solver.time_bound.eval n
  let sel := poly_solver_induces_bounded_selector family solver n
  let ⟨f, hbound, hagree⟩ := tr.transfer n d sel
  exact sideA_bounded_selector_impossible M hub d ⟨f, hagree, fun x _ => hbound x⟩

-- ════════════════════════════════════════════════════════════
-- Step 6: Sovereignty corollary
-- ════════════════════════════════════════════════════════════

/-- Sovereignty from closure conditions: witness sovereignty holds for
    any system where certification implies realization, transport is
    consequence-closed among participants, and aggregation is closed. -/
theorem sovereignty_from_closure
    (S : DistributedWitnessSystem)
    (participants : Finset S.AgentType)
    (h_cert : ∀ a ∈ participants, ∀ s, S.localCertify a s → S.realize a s)
    (h_closed : ∀ a ∈ participants, ∀ b ∈ participants, ∀ s s',
      S.transport a b s s' →
      ∀ d, S.cost s ≤ d → S.realize a s →
        S.cost s' ≤ d + S.transportOverhead ∧ S.realize b s')
    (h_agg : ∀ agg : Aggregation S, agg.contributors ⊆ participants →
      ∀ a ∈ agg.contributors, S.realize a agg.global) :
    WitnessSovereignty S participants :=
  ⟨h_cert,
   fun a ha b hb s s' htrans hreal =>
     (h_closed a ha b hb s s' htrans (S.cost s) (Nat.le_refl _) hreal).2,
   h_agg⟩

-- ════════════════════════════════════════════════════════════
-- Step 7: Protocol witness family
-- ════════════════════════════════════════════════════════════

/-- The five protocol regimes are all instances of DistributedWitnessSystem
    with different transport/projection/realization configurations. -/
structure ProtocolWitnessFamily where
  capability : DistributedWitnessSystem
  consensus : DistributedWitnessSystem
  zk : DistributedWitnessSystem
  coherence_sys : DistributedWitnessSystem
  value_sys : DistributedWitnessSystem

/-- The canonical protocol witness family using our instances. -/
def canonicalProtocolFamily (fc : FinalityCondition) (zk : ZKSystem) :
    ProtocolWitnessFamily where
  capability := capabilityWitnessSystem
  consensus := consensusWitnessSystem fc
  zk := zkWitnessSystem zk
  -- coherence_sys and value_sys both use capabilityWitnessSystem.
  -- This reflects the architectural fact that coherence transport and
  -- value collapse are different ANALYSES of the same capability system,
  -- not distinct systems. The five-field structure exists for API clarity
  -- at call sites, not because the systems are distinct.
  coherence_sys := capabilityWitnessSystem
  value_sys := capabilityWitnessSystem

-- trivialConsequenceFaithful is in Shared/CookFaithfulness.lean.

end ClassicalConstraints
