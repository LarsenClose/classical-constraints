/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

ClassicalConstraints/ZKProjectionInstance.lean — Zero-knowledge proofs as
projection instances. ZK IS projection: it preserves certify (the proof
verifies) and blocks extract (the witness cannot be reconstructed from the
proof).

STATUS: 0 sorry, Classical.choice allowed.
-/

import ClassicalConstraints.Chain7_Protocol.DistributedWitnessCore

namespace ClassicalConstraints

-- ════════════════════════════════════════════════════════════
-- Section 1: ZK proof structures
-- ════════════════════════════════════════════════════════════

/-- A ZK proof state: the projected version of a witness. -/
structure ZKProofState where
  /-- Proof data (opaque, reduced from full witness) -/
  proof_size : Nat
  /-- Whether the proof verifies -/
  verifies : Bool
  /-- The original witness cost (hidden but tracked for comparison) -/
  original_cost : Nat

/-- A ZK system: defines how witnesses are projected into proofs. -/
structure ZKSystem where
  /-- Full witness state type -/
  WitnessState : Type
  /-- Validity predicate on witnesses -/
  witness_valid : WitnessState → Prop
  /-- Cost of a witness -/
  witness_cost : WitnessState → Nat
  /-- The projection: witness → proof -/
  prove : WitnessState → ZKProofState
  /-- Soundness: only valid witnesses produce verifying proofs -/
  h_sound : ∀ w, (prove w).verifies = true → witness_valid w
  /-- Completeness: valid witnesses produce verifying proofs -/
  h_complete : ∀ w, witness_valid w → (prove w).verifies = true
  /-- Zero-knowledge: proof size is bounded independent of witness complexity -/
  h_zk : ∃ bound, ∀ w, (prove w).proof_size ≤ bound

-- ════════════════════════════════════════════════════════════
-- Section 2: ZK witness system instantiation
-- ════════════════════════════════════════════════════════════

/-- The ZK witness system: ZK as a projection instance. -/
def zkWitnessSystem (_zk : ZKSystem) : DistributedWitnessSystem where
  AgentType := Nat
  State := ZKProofState
  cost := ZKProofState.proof_size
  localCertify := fun _ s => s.verifies = true
  -- Proofs transport without change (zero overhead)
  transport := fun _ _ s s' => s = s'
  transportOverhead := 0
  h_transport_cost := fun _ _ _ _ h => by
    simp only [h]; omega
  project := fun s => { s with original_cost := 0 }
  h_project_reduces := fun _ => Nat.le_refl _
  h_project_idempotent := fun _ => rfl
  -- Realization = verification (proof verifies at any agent)
  realize := fun _ s => s.verifies = true

-- ════════════════════════════════════════════════════════════
-- Section 3: Transport collapse (ZK is freely transportable)
-- ════════════════════════════════════════════════════════════

/-- ZK has transport collapse: zero-overhead transport preserves realization. -/
theorem zk_has_transport_collapse (zk : ZKSystem) :
    (zkWitnessSystem zk).TransportCollapse := by
  intro a b s₁ d hcost hreal
  -- Transport is identity: s₂ = s₁
  refine ⟨s₁, rfl, ?_, hreal⟩
  -- cost s₁ ≤ d + 0 = d, which follows from hcost
  simpa using hcost

-- ════════════════════════════════════════════════════════════
-- Section 4: Certification preservation
-- ════════════════════════════════════════════════════════════

/-- ZK preserves certify: valid witnesses produce locally certifiable proofs. -/
theorem zk_preserves_certify (zk : ZKSystem) (a : Nat) (w : zk.WitnessState)
    (h : zk.witness_valid w) :
    (zkWitnessSystem zk).localCertify a (zk.prove w) :=
  zk.h_complete w h

/-- ZK has projection collapse: projection preserves verification. -/
theorem zk_has_projection_collapse (zk : ZKSystem) :
    (zkWitnessSystem zk).ProjectionCollapse := by
  intro a s h
  -- projection strips original_cost but preserves verifies
  exact h

-- ════════════════════════════════════════════════════════════
-- Section 5: Value collapse failure
-- ════════════════════════════════════════════════════════════

/-- ZK does NOT have value collapse: two proofs with the same proof_size
    may have different verification status. Realizability depends on
    structure (verifies), not just cost (proof_size). -/
theorem zk_no_value_collapse (zk : ZKSystem)
    (h_nontrivial : ∃ s₁ s₂ : ZKProofState,
      s₁.proof_size = s₂.proof_size ∧ s₁.verifies = true ∧ s₂.verifies = false) :
    ¬(zkWitnessSystem zk).ValueCollapse := by
  intro hvc
  obtain ⟨s₁, s₂, hsize, hv1, hv2⟩ := h_nontrivial
  have hcost : (zkWitnessSystem zk).cost s₁ = (zkWitnessSystem zk).cost s₂ := hsize
  have hr1 : (zkWitnessSystem zk).realize (0 : Nat) s₁ := hv1
  have hr2 : (zkWitnessSystem zk).realize (0 : Nat) s₂ := (hvc (0 : Nat) s₁ s₂ hcost).mp hr1
  simp only [zkWitnessSystem] at hr2
  rw [hv2] at hr2
  exact absurd hr2 (by decide)

-- ════════════════════════════════════════════════════════════
-- Section 6: Extract blocking
-- ════════════════════════════════════════════════════════════

/-- ZK blocks extract: after projection, the original_cost is stripped.
    A certifiable proof has original_cost = 0, losing all witness depth info. -/
theorem zk_blocks_extract (zk : ZKSystem)
    (w : zk.WitnessState) (hw : zk.witness_valid w) :
    let proj := (zkWitnessSystem zk).project (zk.prove w)
    (zkWitnessSystem zk).localCertify (0 : Nat) proj ∧
    proj.original_cost = 0 := by
  constructor
  · simp only [zkWitnessSystem]
    exact zk.h_complete w hw
  · simp [zkWitnessSystem]

/-- Projection zeroes the original cost of any proof. -/
theorem zk_projection_zeroes_cost (zk : ZKSystem)
    (w : zk.WitnessState) :
    ((zkWitnessSystem zk).project (zk.prove w)).original_cost = 0 := by
  simp [zkWitnessSystem]

-- ════════════════════════════════════════════════════════════
-- Section 7: No launderability
-- ════════════════════════════════════════════════════════════

/-- ZK system does NOT have launderability: transport is identity,
    so realize is preserved trivially (a realized proof stays realized). -/
theorem zk_not_launderable (zk : ZKSystem) :
    ¬(zkWitnessSystem zk).Launderable := by
  intro ⟨a, b, s₁, s₂, htrans, hreal, hnreal⟩
  -- transport is identity: s₂ = s₁
  simp only [zkWitnessSystem] at htrans
  rw [← htrans] at hnreal
  exact hnreal hreal

end ClassicalConstraints
