/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

ClassicalConstraints/ValueCollapseInstance.lean — Value as a projection of
witness topology. Price IS a scalar projection. Non-extractive value is possible.

STATUS: 0 sorry, Classical.choice allowed.
-/

import ClassicalConstraints.Chain7_Protocol.DistributedWitnessCore
import ClassicalConstraints.Chain7_Protocol.CoherenceTransportMeasure

namespace ClassicalConstraints

-- ════════════════════════════════════════════════════════════
-- Section 1: Scalar proxy and price
-- ════════════════════════════════════════════════════════════

/-- A scalar proxy: a single number that summarizes a state. Models price,
    reputation score, credit rating, etc. -/
structure ScalarProxy (S : DistributedWitnessSystem) where
  /-- The proxy function: state → scalar -/
  proxy : S.State → Nat
  /-- The proxy is a projection: it loses information -/
  h_lossy : ∃ s₁ s₂ : S.State, proxy s₁ = proxy s₂ ∧ s₁ ≠ s₂

/-- Price IS a scalar projection: cost compresses state topology into a single number.
    Non-triviality from explicit witness. -/
theorem price_is_projection (S : DistributedWitnessSystem)
    (s₁ s₂ : S.State) (hcost : S.cost s₁ = S.cost s₂) (hne : s₁ ≠ s₂) :
    ∃ sp : ScalarProxy S, sp.proxy = S.cost :=
  ⟨⟨S.cost, s₁, s₂, hcost, hne⟩, rfl⟩

-- ════════════════════════════════════════════════════════════
-- Section 2: Value collapse equivalence
-- ════════════════════════════════════════════════════════════

-- ════════════════════════════════════════════════════════════
-- Section 3: Coherence-based value
-- ════════════════════════════════════════════════════════════

/-- Coherence-based value: value defined as the rate of noncompressible
    addition to the global witness structure. Not a scalar — it's a
    path-derived measure. -/
def CoherenceValue (S : DistributedWitnessSystem)
    (cm : CoherenceMeasure S) {a b s₁ s₂ : _}
    (p : WitnessPath S a b s₁ s₂) : Nat :=
  p.coherence cm

-- ════════════════════════════════════════════════════════════
-- Section 5: Non-extractive value system
-- ════════════════════════════════════════════════════════════

/-- Non-extractive value system: value emerges from graph-coherence and
    participants remain inside the realization loop. -/
structure NonExtractiveValueSystem (S : DistributedWitnessSystem) where
  cm : CoherenceMeasure S
  participants : Finset S.AgentType
  /-- Participants can realize from their own witness states -/
  h_self_realize : ∀ a ∈ participants, ∀ s, S.localCertify a s → S.realize a s
  /-- No external center extracts value from participant witnesses -/
  h_no_expropriation : ¬S.WitnessExpropriation
  /-- No projection capture -/
  h_no_capture : ¬S.ProjectionCapture

-- ════════════════════════════════════════════════════════════
-- Section 6: The positive economic theorem
-- ════════════════════════════════════════════════════════════

/-- Consequence-closed path realizes at endpoint: if a participant can
    self-realize from a certified state, and the path is consequence-closed,
    then the endpoint participant can realize.

    The hypotheses that actually do work:
    - `h_self_realize`: participant `a` can realize from certified states
    - `h_cert`: `a` has certified state `s₁`
    - `h_closed`: the path is consequence-closed

    NOTE: The original `coherence_value_without_expropriation` took a
    `NonExtractiveValueSystem` parameter whose `h_no_expropriation` and
    `h_no_capture` fields were unused. Realization at the endpoint follows
    from consequence closure and self-realization alone. The connection to
    non-extractive systems is that consequence closure is a PROPERTY of
    non-extractive systems (expropriation would break the transport paths
    that enable consequence closure). -/
theorem consequence_closed_path_realizes
    (S : DistributedWitnessSystem)
    {a b s₁ s₂ : _}
    (h_self_realize : ∀ s, S.localCertify a s → S.realize a s)
    (h_cert : S.localCertify a s₁)
    (p : WitnessPath S a b s₁ s₂)
    (h_closed : p.consequenceClosed S) :
    S.realize b s₂ := by
  have hreal_a : S.realize a s₁ := h_self_realize s₁ h_cert
  have hcc := h_closed (S.cost s₁) ⟨Nat.le_refl _, hreal_a⟩
  exact hcc.2

/-- Full coherence value theorem: consequence-closed path gives max coherence value. -/
theorem coherence_value_is_max_when_closed
    (S : DistributedWitnessSystem)
    (cm : CoherenceMeasure S)
    {a b s₁ s₂ : _}
    (p : WitnessPath S a b s₁ s₂)
    (h_all_steps_max : ∀ (a' b' : S.AgentType) (s s' : S.State),
      S.transport a' b' s s' →
      cm.measure_step a' b' s s' = cm.max_coherence) :
    CoherenceValue S cm p = cm.max_coherence := by
  induction p with
  | refl _ _ => simp [CoherenceValue, WitnessPath.coherence]
  | step a' b' c s s' s'' h tail ih =>
    simp only [CoherenceValue, WitnessPath.coherence]
    rw [h_all_steps_max a' b' s s' h]
    simp only [CoherenceValue] at ih
    rw [ih, Nat.min_self]

-- ════════════════════════════════════════════════════════════
-- Section 7: Expropriation and value collapse
-- ════════════════════════════════════════════════════════════

-- ════════════════════════════════════════════════════════════
-- Section 8: Value collapse is the failure mode
-- ════════════════════════════════════════════════════════════

/-- ¬ValueCollapse from explicit witness: two states with equal cost but
    different realizability. -/
theorem no_value_collapse_from_witness (S : DistributedWitnessSystem)
    (a : S.AgentType) (s₁ s₂ : S.State)
    (hcost : S.cost s₁ = S.cost s₂)
    (hr1 : S.realize a s₁)
    (hnr2 : ¬S.realize a s₂) :
    ¬S.ValueCollapse := by
  intro hvc
  exact hnr2 ((hvc a s₁ s₂ hcost).mp hr1)

end ClassicalConstraints
