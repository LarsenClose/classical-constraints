/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

ClassicalConstraints/ConsensusWitnessInstance.lean — Consensus finality as
witness aggregation. WitnessSovereignty definition and structural theorems.

STATUS: 0 sorry, Classical.choice not used.
-/

import ClassicalConstraints.Chain7_Protocol.DistributedWitnessCore

namespace ClassicalConstraints

-- ════════════════════════════════════════════════════════════
-- Section 1: Support and finality structures
-- ════════════════════════════════════════════════════════════

/-- Support: an agent's local endorsement of a state/transaction. -/
structure Support where
  supporter : Nat
  target : Nat
  weight : Nat
  propagation_depth : Nat

/-- Finality condition: threshold for realization. -/
structure FinalityCondition where
  threshold : Nat
  min_supporters : Nat

-- ════════════════════════════════════════════════════════════
-- Section 2: Consensus witness system
-- ════════════════════════════════════════════════════════════

/-- The consensus witness system.

    DESIGN NOTE on weight:
    - `localCertify` requires `weight > 0` (endorsement must have positive strength)
    - `realize` checks only `supporter` and `propagation_depth` (weight excluded)
    - `project` caps weight at 1 via `min s.weight 1`

    Weight is intentionally excluded from realizability: realization depends on
    identity (supporter match) and timing (depth within threshold), not on initial
    endorsement strength. Weight is a certification-time concern — it gates who
    can initially endorse, but once a state exists in the system, its realizability
    depends on structural properties (who supports it, how far it has propagated),
    not on how strongly it was initially endorsed. This means a weight-0 state
    can be realized but not certified, which is consistent: states can enter the
    system through transport (not just certification). -/
def consensusWitnessSystem (fc : FinalityCondition) : DistributedWitnessSystem where
  AgentType := Nat
  State := Support
  cost := Support.propagation_depth
  localCertify := fun a s => s.supporter = a ∧ s.weight > 0
  transport := fun _ b s s' =>
    s'.supporter = b ∧ s'.target = s.target ∧
    s'.propagation_depth = s.propagation_depth + 1 ∧
    s'.weight = s.weight
  transportOverhead := 1
  h_transport_cost := fun _ _ s s' ⟨_, _, hdepth, _⟩ => by
    show s'.propagation_depth ≤ s.propagation_depth + 1; omega
  project := fun s => { s with weight := min s.weight 1 }
  h_project_reduces := fun _ => Nat.le_refl _
  h_project_idempotent := fun s => by
    simp only [Nat.min_assoc, Nat.min_self]
  realize := fun a s => s.supporter = a ∧ s.propagation_depth ≤ fc.threshold

-- ════════════════════════════════════════════════════════════
-- Section 3: Basic properties
-- ════════════════════════════════════════════════════════════

/-- Transport increases propagation_depth by exactly 1. -/
theorem consensus_transport_depth (fc : FinalityCondition) (a b : Nat)
    (s s' : Support) (h : (consensusWitnessSystem fc).transport a b s s') :
    s'.propagation_depth = s.propagation_depth + 1 := h.2.2.1

/-- Consensus does not have transport collapse. -/
theorem consensus_no_transport_collapse (fc : FinalityCondition) :
    ¬(consensusWitnessSystem fc).TransportCollapse := by
  intro h
  -- Take a support at cost 0, realized by agent 0
  let s : Support := ⟨0, 0, 1, 0⟩
  have hreal : (consensusWitnessSystem fc).realize (0 : Nat) s := ⟨rfl, Nat.zero_le _⟩
  obtain ⟨s', htr, hcost, _⟩ := h (0 : Nat) (1 : Nat) s 0 (Nat.le_refl _) hreal
  have hdepth := htr.2.2.1  -- s'.propagation_depth = 0 + 1 = 1
  simp only [consensusWitnessSystem] at hcost
  omega

-- ════════════════════════════════════════════════════════════
-- Section 4: Witness sovereignty
-- ════════════════════════════════════════════════════════════

/-- Witness sovereignty: participants remain inside the realization loop. -/
def WitnessSovereignty (S : DistributedWitnessSystem)
    (participants : Finset S.AgentType) : Prop :=
  -- 1. Every participant who certifies can also realize
  (∀ a ∈ participants, ∀ s, S.localCertify a s → S.realize a s) ∧
  -- 2. Transport among participants preserves realizability
  (∀ a ∈ participants, ∀ b ∈ participants, ∀ s s',
    S.transport a b s s' → S.realize a s → S.realize b s') ∧
  -- 3. Aggregation includes all contributors in realization
  (∀ agg : Aggregation S, agg.contributors ⊆ participants →
    ∀ a ∈ agg.contributors, S.realize a agg.global)

/-- Witness sovereignty from explicit closure conditions. -/
theorem witness_sovereignty_from_closure
    (S : DistributedWitnessSystem) (participants : Finset S.AgentType)
    (h_cert : ∀ a ∈ participants, ∀ s, S.localCertify a s → S.realize a s)
    (h_transport : ∀ a ∈ participants, ∀ b ∈ participants, ∀ s s',
      S.transport a b s s' → S.realize a s → S.realize b s')
    (h_agg : ∀ agg : Aggregation S, agg.contributors ⊆ participants →
      ∀ a ∈ agg.contributors, S.realize a agg.global) :
    WitnessSovereignty S participants :=
  ⟨h_cert, h_transport, h_agg⟩

/-- Sovereignty condition 2 implies consequence-closed transport among participants. -/
theorem sovereignty_implies_transport_closed
    (S : DistributedWitnessSystem) (participants : Finset S.AgentType)
    (h_sov : WitnessSovereignty S participants) :
    ∀ a ∈ participants, ∀ b ∈ participants, ∀ s s',
      S.transport a b s s' → S.realize a s → S.realize b s' :=
  h_sov.2.1

/-- Sovereignty condition 3: aggregations within participants realize for all contributors. -/
theorem sovereignty_implies_agg_closure
    (S : DistributedWitnessSystem) (participants : Finset S.AgentType)
    (h_sov : WitnessSovereignty S participants) :
    ∀ agg : Aggregation S, agg.contributors ⊆ participants →
      ∀ a ∈ agg.contributors, S.realize a agg.global :=
  h_sov.2.2

-- ════════════════════════════════════════════════════════════
-- Section 5: Consensus sovereignty with depth bound
-- ════════════════════════════════════════════════════════════

/-- Consensus sovereignty holds when:
    1. All initial certified states have depth ≤ threshold, AND
    2. All participant-to-participant transports preserve depth ≤ threshold. -/
theorem consensus_sovereignty (fc : FinalityCondition)
    (participants : Finset Nat)
    (h_init : ∀ a ∈ participants, ∀ s,
      (consensusWitnessSystem fc).localCertify a s →
      s.propagation_depth ≤ fc.threshold)
    (h_depth : ∀ a ∈ participants, ∀ b ∈ participants, ∀ s s',
      (consensusWitnessSystem fc).transport a b s s' →
      s'.propagation_depth ≤ fc.threshold) :
    WitnessSovereignty (consensusWitnessSystem fc) participants := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha s hcert
    exact ⟨hcert.1, h_init a ha s hcert⟩
  · intro a ha b hb s s' htr ⟨_, _⟩
    exact ⟨htr.1, h_depth a ha b hb s s' htr⟩
  · intro agg _ a ha
    exact agg.h_realizable a ha

/-- Witness expropriation with participant overlap breaks sovereignty condition 1.
    When the expropriated agents overlap with the sovereignty participants AND
    certification implies realization (projection is identity on realized states),
    the expropriation gives a direct contradiction. -/
theorem expropriation_breaks_sovereignty
    (S : DistributedWitnessSystem) [DecidableEq S.AgentType]
    (participants : Finset S.AgentType)
    (partset : Finset S.AgentType)
    (h_fail : ∀ a ∈ partset, ∃ s, S.localCertify a s ∧ ¬S.realize a (S.project s))
    (h_overlap : (partset ∩ participants).Nonempty)
    (h_proj_id : ∀ a s, S.realize a s → S.project s = s) :
    ¬WitnessSovereignty S participants := by
  intro ⟨h_cert, _, _⟩
  obtain ⟨a, ha_both⟩ := h_overlap
  have ha_part := (Finset.mem_inter.mp ha_both).1
  have ha_participants := (Finset.mem_inter.mp ha_both).2
  obtain ⟨s, hcert, hnreal⟩ := h_fail a ha_part
  have hreal := h_cert a ha_participants s hcert
  rw [h_proj_id a s hreal] at hnreal
  exact hnreal hreal

-- ════════════════════════════════════════════════════════════
-- Section 6: Conservativity
-- ════════════════════════════════════════════════════════════

/-- The consensus system has ProjectionCollapse: projecting a realized state
    gives a state realized by the same agent (depth unchanged by projection). -/
theorem consensus_projection_collapse (fc : FinalityCondition) :
    (consensusWitnessSystem fc).ProjectionCollapse := by
  intro a s ⟨hsupp, hdepth⟩
  exact ⟨hsupp, hdepth⟩

/-- The trivial finality condition (threshold = 0): a realized state must have depth 0. -/
theorem trivial_fc_zero_depth : ∀ a s,
    (consensusWitnessSystem ⟨0, 0⟩).realize a s → s.propagation_depth = 0 := by
  intro a s ⟨_, hdepth⟩
  exact Nat.eq_zero_of_le_zero hdepth

-- ════════════════════════════════════════════════════════════
-- Section 7: Epistemic coordinates
-- ════════════════════════════════════════════════════════════

end ClassicalConstraints
