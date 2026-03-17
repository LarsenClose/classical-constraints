/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

ClassicalConstraints/CoherenceTransportMeasure.lean — Coherence as a
quantitative measure of witness survival across transport steps.
High coherence = consequence-closed. Low coherence = degraded.
Zero coherence = forged/disconnected.

STATUS: 0 sorry, Classical.choice allowed.
-/

import ClassicalConstraints.Chain7_Protocol.DistributedWitnessCore

namespace ClassicalConstraints

-- ════════════════════════════════════════════════════════════
-- Section 1: Coherence measure structure
-- ════════════════════════════════════════════════════════════

/-- Coherence measure: quantifies how much realizability-relevant structure
    survives a transport step. Values in [0, max_coherence]. -/
structure CoherenceMeasure (S : DistributedWitnessSystem) where
  /-- Maximum coherence (fully preserved) -/
  max_coherence : Nat
  /-- Measure a single transport step -/
  measure_step : S.AgentType → S.AgentType → S.State → S.State → Nat
  /-- Coherence is bounded -/
  h_bounded : ∀ a b s s', measure_step a b s s' ≤ max_coherence
  /-- Full coherence iff consequence-closed for that step -/
  h_full_iff_closed : ∀ a b s s',
    S.transport a b s s' →
    (measure_step a b s s' = max_coherence ↔
      ∀ d, S.cost s ≤ d → S.realize a s →
        S.cost s' ≤ d + S.transportOverhead ∧ S.realize b s')
  /-- Zero coherence iff no valid transport exists -/
  h_zero_iff_forged : ∀ a b s s',
    measure_step a b s s' = 0 ↔ ¬S.transport a b s s'

-- ════════════════════════════════════════════════════════════
-- Section 2: Path coherence
-- ════════════════════════════════════════════════════════════

/-- Path coherence: minimum coherence across all steps in a path. -/
def WitnessPath.coherence {S : DistributedWitnessSystem} (cm : CoherenceMeasure S) :
    ∀ {a b s₁ s₂ : _}, WitnessPath S a b s₁ s₂ → Nat
  | _, _, _, _, .refl _ _ => cm.max_coherence
  | _, _, _, _, .step a b _ s₁ s₂ _ _h tail =>
    min (cm.measure_step a b s₁ s₂) (tail.coherence cm)

/-- Coherence threshold: the minimum path coherence for consequence closure. -/
def CoherenceThreshold (S : DistributedWitnessSystem) (cm : CoherenceMeasure S) : Nat :=
  cm.max_coherence

-- ════════════════════════════════════════════════════════════
-- Section 3: Path extension
-- ════════════════════════════════════════════════════════════

/-- Extend a path by one step at the end. -/
def WitnessPath.snoc {S : DistributedWitnessSystem} :
    ∀ {a b c : S.AgentType} {s₁ s₂ s₃ : S.State},
    WitnessPath S a b s₁ s₂ → S.transport b c s₂ s₃ → WitnessPath S a c s₁ s₃
  | _, _, c, _, _, s₃, .refl b s₂, h => .step b c c s₂ s₃ s₃ h (.refl c s₃)
  | _, _, c, _, _, s₃, .step a' b' _ s₁' s₂' _ h' tail, h =>
    .step a' b' c s₁' s₂' s₃ h' (tail.snoc h)

-- ════════════════════════════════════════════════════════════
-- Section 4: Basic coherence properties
-- ════════════════════════════════════════════════════════════

/-- Coherence is bounded by max_coherence for all paths. -/
theorem coherence_bounded {S : DistributedWitnessSystem} (cm : CoherenceMeasure S)
    {a b s₁ s₂ : _} (p : WitnessPath S a b s₁ s₂) :
    p.coherence cm ≤ cm.max_coherence := by
  induction p with
  | refl _ _ => exact Nat.le_refl _
  | step a b _ s₁ s₂ s₃ h tail ih =>
    simp only [WitnessPath.coherence]
    calc min (cm.measure_step a b s₁ s₂) (tail.coherence cm)
        ≤ cm.measure_step a b s₁ s₂ := Nat.min_le_left _ _
      _ ≤ cm.max_coherence := cm.h_bounded a b s₁ s₂

/-- Refl path has max coherence. -/
theorem coherence_refl {S : DistributedWitnessSystem} (cm : CoherenceMeasure S)
    (a : S.AgentType) (s : S.State) :
    (WitnessPath.refl a s).coherence cm = cm.max_coherence :=
  rfl

/-- Adding a step can only decrease coherence. -/
theorem coherence_step_le_tail {S : DistributedWitnessSystem} (cm : CoherenceMeasure S)
    {a b c : S.AgentType} {s₁ s₂ s₃ : S.State}
    (h : S.transport a b s₁ s₂) (tail : WitnessPath S b c s₂ s₃) :
    (WitnessPath.step a b c s₁ s₂ s₃ h tail).coherence cm ≤ tail.coherence cm := by
  simp only [WitnessPath.coherence]
  exact Nat.min_le_right _ _

/-- Adding a step can only decrease coherence (left side). -/
theorem coherence_step_le_head {S : DistributedWitnessSystem} (cm : CoherenceMeasure S)
    {a b c : S.AgentType} {s₁ s₂ s₃ : S.State}
    (h : S.transport a b s₁ s₂) (tail : WitnessPath S b c s₂ s₃) :
    (WitnessPath.step a b c s₁ s₂ s₃ h tail).coherence cm ≤
      cm.measure_step a b s₁ s₂ := by
  simp only [WitnessPath.coherence]
  exact Nat.min_le_left _ _

-- ════════════════════════════════════════════════════════════
-- Section 5: Coherence = max implies consequence closure
-- ════════════════════════════════════════════════════════════

/-- Path consequence closure from uniform consequence closure on steps. -/
theorem path_closed_from_steps {S : DistributedWitnessSystem}
    (h_steps : ∀ (a' b' : S.AgentType) (s s' : S.State),
      S.transport a' b' s s' →
      ∀ d, S.cost s ≤ d → S.realize a' s →
        S.cost s' ≤ d + S.transportOverhead ∧ S.realize b' s') :
    ∀ {a b s₁ s₂ : _} (p : WitnessPath S a b s₁ s₂), p.consequenceClosed S := by
  intro a b s₁ s₂ p
  induction p with
  | refl _ _ =>
    intro d ⟨hcost, hreal⟩
    simp only [WitnessPath.totalOverhead, WitnessPath.length, Nat.zero_mul, Nat.add_zero]
    exact ⟨hcost, hreal⟩
  | step a' b' c s s' s'' h tail ih =>
    intro d ⟨hcost, hreal⟩
    simp only [WitnessPath.totalOverhead, WitnessPath.length] at *
    have ⟨hcost', hreal'⟩ := h_steps a' b' s s' h d hcost hreal
    have ⟨hcost'', hreal''⟩ := ih (d + S.transportOverhead) (And.intro hcost' hreal')
    simp only [WitnessPath.totalOverhead] at hcost''
    refine ⟨?_, hreal''⟩
    have hmul : (1 + tail.length) * S.transportOverhead =
                S.transportOverhead + tail.length * S.transportOverhead := by
      rw [Nat.add_mul, Nat.one_mul]
    omega

/-- Full coherence (= max_coherence) implies step consequence closure. -/
theorem full_coherence_implies_step_closed {S : DistributedWitnessSystem}
    (cm : CoherenceMeasure S)
    {a b c : S.AgentType} {s₁ s₂ s₃ : S.State}
    (h : S.transport a b s₁ s₂) (tail : WitnessPath S b c s₂ s₃)
    (hcoh : (WitnessPath.step a b c s₁ s₂ s₃ h tail).coherence cm = cm.max_coherence) :
    cm.measure_step a b s₁ s₂ = cm.max_coherence ∧
    tail.coherence cm = cm.max_coherence := by
  simp only [WitnessPath.coherence] at hcoh
  constructor
  · have hle := cm.h_bounded a b s₁ s₂
    have hmin := Nat.min_le_left (cm.measure_step a b s₁ s₂) (tail.coherence cm)
    omega
  · have hle := coherence_bounded cm tail
    have hmin := Nat.min_le_right (cm.measure_step a b s₁ s₂) (tail.coherence cm)
    omega

/-- Coherence = max_coherence implies consequence closed. -/
theorem coherence_max_implies_closed {S : DistributedWitnessSystem}
    (cm : CoherenceMeasure S) {a b s₁ s₂ : _}
    (p : WitnessPath S a b s₁ s₂)
    (hcoh : p.coherence cm = cm.max_coherence) :
    p.consequenceClosed S := by
  induction p with
  | refl _ _ =>
    intro d ⟨hcost, hreal⟩
    simp [WitnessPath.totalOverhead, WitnessPath.length]
    exact ⟨hcost, hreal⟩
  | step a' b' c s s' s'' h tail ih =>
    have ⟨hstep_max, htail_max⟩ := full_coherence_implies_step_closed cm h tail hcoh
    have ih_closed := ih htail_max
    intro d ⟨hcost, hreal⟩
    simp only [WitnessPath.totalOverhead, WitnessPath.length,
               Nat.add_mul, Nat.one_mul] at *
    have hstep_closed := (cm.h_full_iff_closed a' b' s s' h).mp hstep_max
    have ⟨hcost', hreal'⟩ := hstep_closed d hcost hreal
    have ⟨hcost'', hreal''⟩ := ih_closed (d + S.transportOverhead) (And.intro hcost' hreal')
    simp only [WitnessPath.totalOverhead] at hcost''
    refine ⟨?_, hreal''⟩
    have hmul : (1 + tail.length) * S.transportOverhead =
                S.transportOverhead + tail.length * S.transportOverhead := by
      rw [Nat.add_mul, Nat.one_mul]
    omega

-- ════════════════════════════════════════════════════════════
-- Section 6: Coherence monotonicity
-- ════════════════════════════════════════════════════════════

/-- Snoc-ing a step decreases coherence (or keeps it the same). -/
theorem coherence_snoc_le {S : DistributedWitnessSystem} (cm : CoherenceMeasure S)
    {a b c : S.AgentType} {s₁ s₂ s₃ : S.State}
    (p : WitnessPath S a b s₁ s₂) (h : S.transport b c s₂ s₃) :
    (p.snoc h).coherence cm ≤ p.coherence cm := by
  induction p with
  | refl b' _ =>
    simp only [WitnessPath.snoc, WitnessPath.coherence]
    exact Nat.min_le_right _ _
  | step a' b' _ s s' s'' h' tail ih =>
    simp only [WitnessPath.snoc, WitnessPath.coherence]
    -- Goal: min step_coh (tail.snoc h).coh ≤ min step_coh tail.coh
    -- ih: (tail.snoc h).coh ≤ tail.coh
    -- Use: min a x ≤ min a y when x ≤ y
    -- Goal: min step_coh (tail.snoc h).coh ≤ min step_coh tail.coh
    -- Use: min a x ≤ a and min a x ≤ x ≤ y (from ih h)
    have hsnoc_le := ih h  -- (tail.snoc h).coh ≤ tail.coh
    have hmin_le_step := Nat.min_le_left (cm.measure_step a' b' s s') (WitnessPath.coherence cm (tail.snoc h))
    have hmin_le_snoc := Nat.min_le_right (cm.measure_step a' b' s s') (WitnessPath.coherence cm (tail.snoc h))
    -- min a x ≤ min a y: show lhs ≤ a and lhs ≤ y
    apply Nat.le_min.mpr
    exact ⟨hmin_le_step, hmin_le_snoc.trans hsnoc_le⟩

-- ════════════════════════════════════════════════════════════
-- Section 7: Below-threshold implies degraded step
-- ════════════════════════════════════════════════════════════

/-- Below-threshold coherence implies at least one step has low coherence. -/
theorem below_threshold_has_degraded_step {S : DistributedWitnessSystem}
    (cm : CoherenceMeasure S)
    {a b s₁ s₂ : _} (p : WitnessPath S a b s₁ s₂)
    (h : p.coherence cm < cm.max_coherence) :
    ∃ (a' b' : S.AgentType) (s s' : S.State),
      S.transport a' b' s s' ∧
      cm.measure_step a' b' s s' < cm.max_coherence := by
  induction p with
  | refl _ _ =>
    simp only [WitnessPath.coherence] at h
    exact absurd h (Nat.lt_irrefl _)
  | step a' b' _ s s' _ htrans tail ih =>
    simp only [WitnessPath.coherence] at h
    by_cases hstep : cm.measure_step a' b' s s' < cm.max_coherence
    · exact ⟨a', b', s, s', htrans, hstep⟩
    · push_neg at hstep
      have hstep_max : cm.measure_step a' b' s s' = cm.max_coherence :=
        Nat.le_antisymm (cm.h_bounded a' b' s s') hstep
      rw [hstep_max] at h
      have htail_lt : tail.coherence cm < cm.max_coherence := by
        have := Nat.min_le_right cm.max_coherence (tail.coherence cm)
        omega
      exact ih htail_lt

-- ════════════════════════════════════════════════════════════
-- Section 8: Coherence composition
-- ════════════════════════════════════════════════════════════

/-- Coherence composes via min: bounded by each component. -/
theorem coherence_of_composition_le_max {S : DistributedWitnessSystem}
    (cm : CoherenceMeasure S) (c₁ c₂ : Nat)
    (hc1 : c₁ ≤ cm.max_coherence) :
    min c₁ c₂ ≤ cm.max_coherence :=
  (Nat.min_le_left c₁ c₂).trans hc1

/-- Full-coherence steps compose to full-coherence paths. -/
theorem full_coherence_composes {S : DistributedWitnessSystem}
    (cm : CoherenceMeasure S)
    {a b c : S.AgentType} {s₁ s₂ s₃ : S.State}
    (h : S.transport a b s₁ s₂)
    (hstep : cm.measure_step a b s₁ s₂ = cm.max_coherence)
    (tail : WitnessPath S b c s₂ s₃)
    (htail : tail.coherence cm = cm.max_coherence) :
    (WitnessPath.step a b c s₁ s₂ s₃ h tail).coherence cm = cm.max_coherence := by
  simp only [WitnessPath.coherence, hstep, htail, Nat.min_self]

-- ════════════════════════════════════════════════════════════
-- Section 9: Non-forged steps have positive coherence
-- ════════════════════════════════════════════════════════════

/-- A transport that actually holds has positive coherence
    (h_zero_iff_forged contrapositive). -/
theorem transport_implies_pos_coherence {S : DistributedWitnessSystem}
    (cm : CoherenceMeasure S)
    {a b : S.AgentType} {s s' : S.State}
    (h : S.transport a b s s')
    (_hmax : cm.max_coherence > 0) :
    cm.measure_step a b s s' > 0 := by
  by_contra hle
  push_neg at hle
  have heq : cm.measure_step a b s s' = 0 := Nat.eq_zero_of_le_zero hle
  rw [cm.h_zero_iff_forged] at heq
  exact heq h

-- ════════════════════════════════════════════════════════════
-- Section 10: Consequence closure implies max coherence (partial)
-- ════════════════════════════════════════════════════════════

/-- Single step: consequence closure implies full coherence. -/
theorem step_closed_implies_full_coherence {S : DistributedWitnessSystem}
    (cm : CoherenceMeasure S)
    {a b : S.AgentType} {s s' : S.State}
    (h : S.transport a b s s')
    (hclosed : ∀ d, S.cost s ≤ d → S.realize a s →
      S.cost s' ≤ d + S.transportOverhead ∧ S.realize b s') :
    cm.measure_step a b s s' = cm.max_coherence :=
  (cm.h_full_iff_closed a b s s' h).mpr hclosed

-- ════════════════════════════════════════════════════════════
-- Section 11: Epistemic coordinates
-- ════════════════════════════════════════════════════════════

/-- CoherenceTransportMeasure epistemic level: 2. -/
def coherenceTransportMeasure_level : Nat := 2

end ClassicalConstraints
