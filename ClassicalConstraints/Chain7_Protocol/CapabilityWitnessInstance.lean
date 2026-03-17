/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

ClassicalConstraints/CapabilityWitnessInstance.lean — Delegation chains
as transport paths in the capability witness system.

STATUS: 0 sorry, Classical.choice not needed.
-/

import ClassicalConstraints.Chain7_Protocol.DistributedWitnessCore

namespace ClassicalConstraints

-- ════════════════════════════════════════════════════════════
-- Section 1: Capability structures
-- ════════════════════════════════════════════════════════════

/-- A capability: a typed authorization that an agent holds. -/
structure Capability where
  holder : Nat  -- agent id
  right : String
  /-- Delegation depth: how many times this capability has been delegated -/
  depth : Nat
  /-- Whether the capability is still exercisable -/
  active : Bool

/-- A delegation step: agent A authorizes agent B to hold a capability. -/
structure DelegationStep where
  delegator : Nat
  delegate : Nat
  cap : Capability
  /-- The delegator holds the capability -/
  h_held : cap.holder = delegator
  /-- The delegated capability has incremented depth -/
  delegated_cap : Capability
  /-- The delegated capability matches expectations -/
  h_delegated : delegated_cap.holder = delegate ∧
                delegated_cap.depth = cap.depth + 1 ∧
                delegated_cap.right = cap.right ∧
                delegated_cap.active = cap.active

/-- Maximum delegation depth before capabilities become unrealizable. -/
def maxDelegationDepth : Nat := 100

-- ════════════════════════════════════════════════════════════
-- Section 2: Capability witness system instantiation
-- ════════════════════════════════════════════════════════════

/-- The capability witness system: delegation as transport. -/
def capabilityWitnessSystem : DistributedWitnessSystem where
  AgentType := Nat
  State := Capability
  cost := Capability.depth
  localCertify := fun a c => c.holder = a ∧ c.active = true
  transport := fun a b s s' =>
    ∃ d : DelegationStep, d.delegator = a ∧ d.delegate = b ∧
      d.cap = s ∧ d.delegated_cap = s'
  transportOverhead := 1
  h_transport_cost := by
    intro a b s s' ⟨d, _, _, hs, hs'⟩
    -- s = d.cap, s' = d.delegated_cap
    -- d.h_delegated : delegated_cap.depth = cap.depth + 1
    rw [← hs, ← hs']
    exact Nat.le_of_eq d.h_delegated.2.1
  project := fun c => { c with active := true }
  h_project_reduces := fun c => Nat.le_refl _
  h_project_idempotent := fun c => by simp
  realize := fun a c => c.holder = a ∧ c.active = true ∧ c.depth ≤ maxDelegationDepth

-- ════════════════════════════════════════════════════════════
-- Section 3: Basic properties
-- ════════════════════════════════════════════════════════════

/-- Delegation overhead is exactly 1. -/
theorem delegation_overhead_is_one :
    capabilityWitnessSystem.transportOverhead = 1 := rfl

/-- Delegation IS transport: every DelegationStep corresponds to a transport step. -/
theorem delegation_is_transport (d : DelegationStep) :
    capabilityWitnessSystem.transport d.delegator d.delegate d.cap d.delegated_cap :=
  ⟨d, rfl, rfl, rfl, rfl⟩

/-- The capability system is locally certifiable: active capabilities are locally certified. -/
theorem active_cap_locally_certified (a : capabilityWitnessSystem.AgentType) (c : Capability)
    (h_holder : c.holder = a) (h_active : c.active = true) :
    capabilityWitnessSystem.localCertify a c :=
  ⟨h_holder, h_active⟩

-- ════════════════════════════════════════════════════════════
-- Section 4: Transport collapse obstruction
-- ════════════════════════════════════════════════════════════

/-- The capability system does NOT have transport collapse:
    delegation always adds depth (overhead = 1 ≠ 0). -/
theorem capability_no_transport_collapse :
    ¬capabilityWitnessSystem.TransportCollapse := by
  intro h
  -- TransportCollapse requires: for any realized capability, there's a transported
  -- state with cost ≤ original cost and realized by the target.
  -- But transport always increases depth by 1, so cost goes up.
  -- Specifically: take any active capability c at maxDelegationDepth.
  let c : Capability := ⟨0, "test", maxDelegationDepth, true⟩
  have hcert : capabilityWitnessSystem.realize (0 : Nat) c := ⟨rfl, rfl, Nat.le_refl _⟩
  -- TransportCollapse from agent 0 to agent 1 at d = maxDelegationDepth
  obtain ⟨s₂, ⟨d, _, _, hcap, hs'⟩, hcost, hreal⟩ := h (0 : Nat) (1 : Nat) c maxDelegationDepth
    (Nat.le_refl _) hcert
  -- hcost : capabilityWitnessSystem.cost s₂ ≤ maxDelegationDepth
  -- hcap : d.cap = c, so d.cap.depth = maxDelegationDepth
  -- hs' : d.delegated_cap = s₂, so d.delegated_cap.depth = s₂.depth
  -- d.h_delegated.2.1 : d.delegated_cap.depth = d.cap.depth + 1
  have hdepth := d.h_delegated.2.1
  -- hdepth : d.delegated_cap.depth = d.cap.depth + 1
  have hcap_depth : d.cap.depth = maxDelegationDepth := by rw [hcap]
  have hs2_depth : s₂.depth = d.delegated_cap.depth := by rw [← hs']
  show False
  simp only [capabilityWitnessSystem] at hcost
  omega

-- ════════════════════════════════════════════════════════════
-- Section 5: Depth and realizability
-- ════════════════════════════════════════════════════════════

/-- Transport increases depth by exactly 1 per step. -/
theorem transport_depth_increment (a b : capabilityWitnessSystem.AgentType) (s s' : Capability)
    (h : capabilityWitnessSystem.transport a b s s') :
    s'.depth = s.depth + 1 := by
  obtain ⟨d, _, _, hs, hs'⟩ := h
  rw [← hs, ← hs']
  exact d.h_delegated.2.1

/-- After k transport steps, depth increases by at most k. -/
theorem witnessPath_depth_bound {a b s₁ s₂ : _}
    (p : WitnessPath capabilityWitnessSystem a b s₁ s₂) :
    s₂.depth ≤ s₁.depth + p.length := by
  have := witnessPath_cost_bound p
  simp only [capabilityWitnessSystem] at this
  simp only [Nat.mul_one] at this
  exact this

/-- A capability realizable at the start of a chain has depth ≤ maxDelegationDepth. -/
theorem realizable_depth_bounded (a : Nat) (c : Capability)
    (h : capabilityWitnessSystem.realize a c) :
    c.depth ≤ maxDelegationDepth :=
  h.2.2

-- ════════════════════════════════════════════════════════════
-- Section 6: Delegation requires consequence closure
-- ════════════════════════════════════════════════════════════

/-- Forward direction: consequence closure implies the final state is realizable
    when the path is short enough (depth stays within bounds). -/
theorem consequence_closure_implies_realizable
    {a b s₁ s₂ : _}
    (chain : WitnessPath capabilityWitnessSystem a b s₁ s₂)
    (h_start : capabilityWitnessSystem.realize a s₁)
    (h_closed : chain.consequenceClosed capabilityWitnessSystem) :
    capabilityWitnessSystem.realize b s₂ := by
  have hd := h_start.2.2  -- s₁.depth ≤ maxDelegationDepth
  -- Apply consequence closure at d = s₁.depth (which is the cost)
  have := h_closed s₁.depth ⟨Nat.le_refl _, h_start⟩
  exact this.2

/-- Laundered capability: a capability with depth exceeding maxDelegationDepth
    is unrealizable. This is the structural characterization of "laundering" —
    a capability that has been delegated too many times loses its realizability. -/
theorem laundered_capability_unrealizable (c : Capability)
    (h_deep : c.depth > maxDelegationDepth) :
    ∀ a : capabilityWitnessSystem.AgentType, ¬capabilityWitnessSystem.realize a c := by
  intro a ⟨_, _, hdepth⟩
  exact absurd hdepth (by omega)

-- ════════════════════════════════════════════════════════════
-- Section 7: Structural properties
-- ════════════════════════════════════════════════════════════

/-- Projection makes any capability active. -/
theorem projection_activates (c : Capability) :
    (capabilityWitnessSystem.project c).active = true := rfl

/-- Projection preserves depth (cost). -/
theorem projection_preserves_depth (c : Capability) :
    (capabilityWitnessSystem.project c).depth = c.depth := rfl

/-- Projection preserves holder. -/
theorem projection_preserves_holder (c : Capability) :
    (capabilityWitnessSystem.project c).holder = c.holder := rfl

/-- An inactive capability can be reactivated by projection. -/
theorem inactive_reactivated_by_projection (a : capabilityWitnessSystem.AgentType) (c : Capability)
    (h_holder : c.holder = a) (h_depth : c.depth ≤ maxDelegationDepth) :
    capabilityWitnessSystem.realize a (capabilityWitnessSystem.project c) :=
  ⟨h_holder, rfl, h_depth⟩

/-- Projection collapse holds for capability system:
    active capabilities remain realizable after projection
    (projection just ensures active = true). -/
theorem capability_projection_collapse :
    capabilityWitnessSystem.ProjectionCollapse := by
  intro a c ⟨h_holder, h_active, h_depth⟩
  exact ⟨h_holder, rfl, h_depth⟩

-- ════════════════════════════════════════════════════════════
-- Section 8: Value collapse fails
-- ════════════════════════════════════════════════════════════

/-- Value collapse fails for capability system:
    two capabilities at the same depth can differ in holdership or activity,
    making realizability depend on more than just cost (depth). -/
theorem capability_no_value_collapse :
    ¬capabilityWitnessSystem.ValueCollapse := by
  intro hvc
  -- Two capabilities at the same depth (cost = 1), one active (realizable), one inactive (not)
  let c1 : Capability := ⟨0, "x", 1, true⟩
  let c2 : Capability := ⟨0, "x", 1, false⟩
  -- cost c1 = cost c2 = 1
  have hcost : capabilityWitnessSystem.cost c1 = capabilityWitnessSystem.cost c2 := rfl
  -- realize 0 c1 (active and within depth)
  have hr1 : capabilityWitnessSystem.realize (0 : Nat) c1 :=
    ⟨rfl, rfl, by decide⟩
  -- realize 0 c2 fails (inactive)
  have hnr2 : ¬capabilityWitnessSystem.realize (0 : Nat) c2 := by
    intro ⟨_, h, _⟩; exact absurd h (by decide)
  exact hnr2 ((hvc (0 : Nat) c1 c2 hcost).mp hr1)

-- ════════════════════════════════════════════════════════════
-- Section 9: Epistemic coordinates
-- ════════════════════════════════════════════════════════════

/-- CapabilityWitnessInstance epistemic level: 2. -/
def capabilityWitnessInstance_level : Nat := 2

end ClassicalConstraints
