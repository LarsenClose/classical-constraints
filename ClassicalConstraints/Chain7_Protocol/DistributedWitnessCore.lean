/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

ClassicalConstraints/DistributedWitnessCore.lean — Four-primitive distributed
witness system: LocalWitness, Transport, Projection, Realization. Three collapse
notions: TransportCollapse, ProjectionCollapse, ValueCollapse. Failure mode
definitions: Forgeable, Launderable, WitnessExpropriation, PanopticonAsymmetry,
ProjectionCapture, DetachedRealization.

STATUS: 0 sorry, no Classical.choice.
-/

import ClassicalConstraints.Shared.CookSelectorBridge
import ClassicalConstraints.Shared.CookFaithfulness
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Basic

namespace ClassicalConstraints

-- ════════════════════════════════════════════════════════════
-- Section 1: Core structure (fixed universes for concrete instances)
-- ════════════════════════════════════════════════════════════

/-- The core structure: a distributed witness system with four primitives.
    Fixed to Type 0 for compatibility with concrete instances. -/
structure DistributedWitnessSystem where
  /-- Agent type -/
  AgentType : Type
  /-- State space -/
  State : Type
  /-- Cost measure on states (analogue of grade) -/
  cost : State → Nat
  /-- LocalWitness: agent can certify a fact from local state -/
  localCertify : AgentType → State → Prop
  /-- Transport: state can move from one agent-context to another -/
  transport : AgentType → AgentType → State → State → Prop
  /-- Transport has bounded overhead -/
  transportOverhead : Nat
  /-- Transport respects cost bound -/
  h_transport_cost : ∀ a b s s',
    transport a b s s' → cost s' ≤ cost s + transportOverhead
  /-- Projection: state can be compressed -/
  project : State → State
  /-- Projection reduces cost -/
  h_project_reduces : ∀ s, cost (project s) ≤ cost s
  /-- Projection is idempotent -/
  h_project_idempotent : ∀ s, project (project s) = project s
  /-- Realization: a state can drive action -/
  realize : AgentType → State → Prop

-- ════════════════════════════════════════════════════════════
-- Section 2: Witness paths
-- ════════════════════════════════════════════════════════════

/-- A path through the witness system: a sequence of transport steps. -/
inductive WitnessPath (S : DistributedWitnessSystem) :
    S.AgentType → S.AgentType → S.State → S.State → Type where
  | refl (a : S.AgentType) (s : S.State) : WitnessPath S a a s s
  | step (a b c : S.AgentType) (s₁ s₂ s₃ : S.State)
      (h : S.transport a b s₁ s₂)
      (tail : WitnessPath S b c s₂ s₃) :
      WitnessPath S a c s₁ s₃

/-- Path length: number of transport steps. -/
def WitnessPath.length : ∀ {S : DistributedWitnessSystem} {a b s₁ s₂ : _},
    WitnessPath S a b s₁ s₂ → Nat
  | _, _, _, _, _, .refl _ _ => 0
  | _, _, _, _, _, .step _ _ _ _ _ _ _ tail => 1 + tail.length

/-- Path total overhead: length × per-step overhead. -/
def WitnessPath.totalOverhead {S : DistributedWitnessSystem} {a b s₁ s₂ : _}
    (p : WitnessPath S a b s₁ s₂) : Nat :=
  p.length * S.transportOverhead

/-- Consequence closure for a path: realizability is preserved
    along the entire path, accounting for accumulated overhead. -/
def WitnessPath.consequenceClosed (S : DistributedWitnessSystem) {a b s₁ s₂ : _}
    (p : WitnessPath S a b s₁ s₂) : Prop :=
  ∀ d, S.cost s₁ ≤ d ∧ S.realize a s₁ →
    S.cost s₂ ≤ d + p.totalOverhead ∧ S.realize b s₂

/-- Path cost bound: endpoint cost ≤ start cost + total overhead. -/
theorem witnessPath_cost_bound {S : DistributedWitnessSystem} {a b s₁ s₂ : _}
    (p : WitnessPath S a b s₁ s₂) :
    S.cost s₂ ≤ S.cost s₁ + p.length * S.transportOverhead := by
  induction p with
  | refl _ _ => simp [WitnessPath.length]
  | step a b c s₁ s₂ s₃ h tail ih =>
    have hstep := S.h_transport_cost a b s₁ s₂ h
    simp only [WitnessPath.length]
    have hmul : (1 + tail.length) * S.transportOverhead =
                S.transportOverhead + tail.length * S.transportOverhead := by
      rw [Nat.add_mul, Nat.one_mul]
    rw [hmul]
    omega

/-- The refl path has zero overhead. -/
theorem witnessPath_refl_overhead {S : DistributedWitnessSystem} (a : S.AgentType) (s : S.State) :
    (WitnessPath.refl a s).totalOverhead = 0 := by
  simp [WitnessPath.totalOverhead, WitnessPath.length]

-- ════════════════════════════════════════════════════════════
-- Section 3: Three collapse notions
-- ════════════════════════════════════════════════════════════

/-- TransportCollapse: a transported witness can be realized at the
    SAME cost as the original (zero overhead collapse). -/
def DistributedWitnessSystem.TransportCollapse (S : DistributedWitnessSystem) : Prop :=
  ∀ (a b : S.AgentType) (s₁ : S.State) (d : Nat),
    S.cost s₁ ≤ d → S.realize a s₁ →
    ∃ s₂, S.transport a b s₁ s₂ ∧ S.cost s₂ ≤ d ∧ S.realize b s₂

/-- ProjectionCollapse: projection preserves realizability. -/
def DistributedWitnessSystem.ProjectionCollapse (S : DistributedWitnessSystem) : Prop :=
  ∀ (a : S.AgentType) (s : S.State),
    S.realize a s → S.realize a (S.project s)

/-- ValueCollapse: cost measure alone determines realizability. -/
def DistributedWitnessSystem.ValueCollapse (S : DistributedWitnessSystem) : Prop :=
  ∀ (a : S.AgentType) (s₁ s₂ : S.State),
    S.cost s₁ = S.cost s₂ → (S.realize a s₁ ↔ S.realize a s₂)

-- ════════════════════════════════════════════════════════════
-- Section 4: Aggregation
-- ════════════════════════════════════════════════════════════

/-- Aggregation: local witnesses compose into a global witness. -/
structure Aggregation (S : DistributedWitnessSystem) where
  contributors : Finset S.AgentType
  local_witnesses : ∀ a ∈ contributors, S.State
  h_certified : ∀ a (ha : a ∈ contributors), S.localCertify a (local_witnesses a ha)
  global : S.State
  h_realizable : ∀ a ∈ contributors, S.realize a global

-- ════════════════════════════════════════════════════════════
-- Section 5: Collapse hierarchy
-- ════════════════════════════════════════════════════════════

/-- Value collapse implies projection collapse when projection preserves cost. -/
theorem value_collapse_implies_projection
    (S : DistributedWitnessSystem)
    (h_vc : S.ValueCollapse)
    (h_cost : ∀ (a : S.AgentType) (s : S.State), S.realize a s →
      S.cost (S.project s) = S.cost s) :
    S.ProjectionCollapse := by
  intro a s hrs
  exact (h_vc a s (S.project s) (h_cost a s hrs).symm).mp hrs

/-- Value collapse is strictly stronger than projection collapse:
    there exist systems with projection collapse but not value collapse. -/
theorem projection_not_implies_value :
    ∃ S : DistributedWitnessSystem, S.ProjectionCollapse ∧ ¬S.ValueCollapse := by
  -- A system with State = Bool, cost = fun _ => 1
  -- realize a true = True, realize a false = False
  -- project = id (so ProjectionCollapse trivially holds)
  -- ValueCollapse fails: cost true = cost false = 1 but realizability differs.
  refine ⟨⟨Unit, Bool, fun _ => 1, fun _ _ => True,
           fun _ _ _ _ => False, 0,
           fun _ _ _ _ h => h.elim,
           id, fun _ => Nat.le_refl _, fun _ => rfl,
           fun _ s => s = true⟩,
           ?_, ?_⟩
  · -- ProjectionCollapse: project = id, so realize a s → realize a (id s) = realize a s
    intro _ s hrs; exact hrs
  · -- ¬ValueCollapse: cost true = cost false but realize ⊤ true ≠ realize ⊤ false
    intro hvc
    have h := (hvc () true false rfl).mp rfl
    -- h : false = true (from realize () false = (false = true))
    exact absurd h (by decide)

/-- Transport collapse gives projection collapse when project is a
    zero-cost identity on realized states. -/
theorem transport_collapse_implies_projection_conditional
    (S : DistributedWitnessSystem)
    (_h_tc : S.TransportCollapse)
    (h_proj_id : ∀ a s, S.realize a s → S.project s = s) :
    S.ProjectionCollapse := by
  intro a s hrs
  rw [h_proj_id a s hrs]
  exact hrs

-- ════════════════════════════════════════════════════════════
-- Section 6: Failure modes
-- ════════════════════════════════════════════════════════════

/-- Failure mode: forgeability. -/
def DistributedWitnessSystem.Forgeable (S : DistributedWitnessSystem) : Prop :=
  ∃ a s, S.localCertify a s ∧
    ∀ b, b ≠ a → ¬∃ s', S.transport a b s s' ∧ S.localCertify b s'

/-- Failure mode: laundering. -/
def DistributedWitnessSystem.Launderable (S : DistributedWitnessSystem) : Prop :=
  ∃ a b s₁ s₂, S.transport a b s₁ s₂ ∧ S.realize a s₁ ∧ ¬S.realize b s₂

/-- Failure mode: aggregation failure. -/
def DistributedWitnessSystem.AggregationFailure (S : DistributedWitnessSystem) : Prop :=
  ∃ (agents : Finset S.AgentType) (local_ws : ∀ a ∈ agents, S.State),
    (∀ a (ha : a ∈ agents), S.localCertify a (local_ws a ha)) ∧
    ¬∃ agg : Aggregation S, agg.contributors = agents

/-- Failure mode: witness expropriation. -/
def DistributedWitnessSystem.WitnessExpropriation (S : DistributedWitnessSystem) : Prop :=
  ∃ (center : S.AgentType) (participants : Finset S.AgentType),
    (∀ a ∈ participants, ∃ s, S.localCertify a s) ∧
    (∀ a ∈ participants, ∀ s, S.localCertify a s →
      S.realize center (S.project s)) ∧
    (∀ a ∈ participants, ∃ s, S.localCertify a s ∧
      ¬S.realize a (S.project s))

/-- Failure mode: panopticon asymmetry. -/
def DistributedWitnessSystem.PanopticonAsymmetry (S : DistributedWitnessSystem) : Prop :=
  ∃ (center : S.AgentType) (participants : Finset S.AgentType),
    (∀ a ∈ participants, ∀ s, S.localCertify a s →
      ∃ s', S.transport a center s s') ∧
    (∀ a ∈ participants, ∀ s, S.realize center s →
      ¬∃ s', S.transport center a s s' ∧ S.realize a s')

/-- Failure mode: projection capture. -/
def DistributedWitnessSystem.ProjectionCapture (S : DistributedWitnessSystem) : Prop :=
  ∃ (center : S.AgentType) (participants : Finset S.AgentType),
    (∀ s, S.realize center (S.project s)) ∧
    (∀ a s, S.localCertify a s → S.localCertify a (S.project s)) ∧
    (∀ a ∈ participants, ∃ s, S.localCertify a s ∧
      S.realize a s ∧ ¬S.realize a (S.project s))

/-- Detached realization: realization by an agent outside the consequence loop. -/
def DistributedWitnessSystem.DetachedRealization (S : DistributedWitnessSystem) : Prop :=
  ∃ (a b : S.AgentType) (s₁ s₂ : S.State),
    S.localCertify a s₁ ∧ S.transport a b s₁ s₂ ∧
    S.realize b s₂ ∧ ¬S.localCertify b s₂

-- ════════════════════════════════════════════════════════════
-- Section 7: Aggregation theorems
-- ════════════════════════════════════════════════════════════

/-- Aggregation from a common realizable global state. -/
theorem aggregation_from_realizable_global
    (S : DistributedWitnessSystem)
    (agents : Finset S.AgentType)
    (local_ws : ∀ a ∈ agents, S.State)
    (h_cert : ∀ a (ha : a ∈ agents), S.localCertify a (local_ws a ha))
    (global : S.State)
    (h_global : ∀ a ∈ agents, S.realize a global) :
    ∃ agg : Aggregation S, agg.contributors = agents :=
  ⟨⟨agents, local_ws, h_cert, global, h_global⟩, rfl⟩

-- ════════════════════════════════════════════════════════════
-- Section 8: SAT witness encoding and bounded selector
-- ════════════════════════════════════════════════════════════

/-- A SAT witness encoding: maps a SAT instance into a witness system. -/
structure SATWitnessEncoding (S : DistributedWitnessSystem) (inst : SATInstance) where
  enc_agent : S.AgentType
  encode : inst.Assignment → S.State
  h_cost : ∀ a, S.cost (encode a) ≤ inst.num_vars
  h_certified : ∀ a, inst.instanceSatisfied a = true →
    S.localCertify enc_agent (encode a)
  h_correct : ∀ a, S.localCertify enc_agent (encode a) →
    inst.instanceSatisfied a = true

-- TODO: Connect transport collapse to bounded selector correctness.
-- The intended claim is that transport collapse on a SAT-encoded system
-- yields a bounded selector that agrees with instanceSatisfied.
-- This requires showing that transport collapse's cost preservation
-- combined with the encoding's faithfulness yields a capacity-bounded
-- decision procedure. Removed: previous version returned BoundedSelector.trivial
-- ignoring both the encoding and the transport collapse hypothesis.

-- ════════════════════════════════════════════════════════════
-- Section 9: Path concatenation
-- ════════════════════════════════════════════════════════════

/-- Concatenate two witness paths. -/
def WitnessPath.concat : ∀ {S : DistributedWitnessSystem} {a b c s₁ s₂ s₃ : _},
    WitnessPath S a b s₁ s₂ → WitnessPath S b c s₂ s₃ → WitnessPath S a c s₁ s₃
  | _, _, _, _, _, _, _, .refl _ _, q => q
  | _, _, _, _, _, _, _, .step a b _ s₁ s₂ _ h tail, q =>
      .step a b _ s₁ s₂ _ h (tail.concat q)

/-- Length of concatenated path is sum of lengths. -/
theorem witnessPath_concat_length {S : DistributedWitnessSystem} {a b c s₁ s₂ s₃ : _}
    (p : WitnessPath S a b s₁ s₂) (q : WitnessPath S b c s₂ s₃) :
    (p.concat q).length = p.length + q.length := by
  induction p with
  | refl _ _ => simp [WitnessPath.concat, WitnessPath.length]
  | step a b c' s₁' s₂' s₃' h tail ih =>
    simp only [WitnessPath.concat, WitnessPath.length]
    have := ih q
    omega

-- ════════════════════════════════════════════════════════════
-- Section 10: Structural counterexamples
-- ════════════════════════════════════════════════════════════

/-- Forgeable and launderable are distinct: a system with no transport
    can be forgeable but not launderable. -/
theorem forgeable_not_implies_launderable :
    ∃ S : DistributedWitnessSystem, S.Forgeable ∧ ¬S.Launderable :=
  ⟨⟨Nat, Nat, id, fun _ _ => True, fun _ _ _ _ => False, 0,
    fun _ _ _ _ h => h.elim,
    id, fun _ => Nat.le_refl _, fun _ => rfl,
    fun _ _ => True⟩,
   ⟨0, 0, trivial, fun _ _ ⟨_, htr, _⟩ => htr⟩,
   fun ⟨_, _, _, _, htr, _, _⟩ => htr⟩

/-- ValueCollapse is consistent: the trivial single-state system has ValueCollapse. -/
theorem trivial_value_collapse :
    ∃ S : DistributedWitnessSystem, S.ValueCollapse :=
  ⟨⟨Unit, Unit, fun _ => 0, fun _ _ => True, fun _ _ _ _ => True, 0,
    fun _ _ _ _ _ => Nat.le_refl _,
    id, fun _ => Nat.le_refl _, fun _ => rfl,
    fun _ _ => True⟩,
   fun _ _ _ _ => Iff.rfl⟩

end ClassicalConstraints
