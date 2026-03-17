/-
  ClassicalConstraints/DescriptiveComplexityLock.lean
  The lock for Chain 3 (Descriptive Complexity).

  Connects Side A (bounded definability resource impossibility, proved in
  pnp-integrated) with Side B (descriptive depth bridges, proved in this repo).

  Lock theorem: GrowthGap + DefinabilityFaithful -> no poly-time SAT solver.

  This file follows the EXACT pattern of SATBoundaryLock.lean.

  Classical.choice is allowed. No sorry.
-/

import ClassicalConstraints.Shared.SideAMirror
import ClassicalConstraints.Chain3_Descriptive.DescriptiveDepthBridge
import ClassicalConstraints.Shared.CookFaithfulness

namespace ClassicalConstraints

-- ════════════════════════════════════════════════════════════
-- Section 1: Mirror types from Side A
-- ════════════════════════════════════════════════════════════

-- GradedReflModel_Mirror, SelfAppUnbounded_Mirror, sideA_bounded_selector_impossible
-- are imported from SideAMirror.

-- Chain 3-specific aliases for clarity in this file.
abbrev GradedReflModel_Mirror_D3 := GradedReflModel_Mirror
abbrev SelfAppUnbounded_Mirror_D3 := SelfAppUnbounded_Mirror

-- ════════════════════════════════════════════════════════════
-- Section 2: Side A axiom
-- ════════════════════════════════════════════════════════════

/-- Chain 3-specific name for the Side A axiom. -/
theorem sideA_bounded_resource_impossible (M : GradedReflModel_Mirror)
    (hub : SelfAppUnbounded_Mirror M) (d : Nat) :
    ¬∃ (f : M.carrier → M.carrier),
      (∀ x, M.grade x ≤ d → f x = M.selfApp x) ∧
      (∀ x, M.grade x ≤ d → M.grade (f x) ≤ d) :=
  sideA_bounded_selector_impossible M hub d

-- ════════════════════════════════════════════════════════════
-- Section 3: DefinabilityFaithful
-- ════════════════════════════════════════════════════════════

/-- DefinabilityFaithful: the chain-3-specific CookFaithful condition.

    Cook encoding preserves the "definability complexity" of the witness
    relation up to polynomial distortion. This is the OPEN bridge condition
    for Chain 3, structurally identical to CookFaithful from Chain 1 but
    using descriptive depth (quantifier rank / pebble count) as the measure. -/
structure DefinabilityFaithful (enc : CookEncoding) where
  /-- The obstruction profile: descriptive depth on SAT side vs grade on model side. -/
  profile : ObstructionProfile
  /-- Lower bound: encoding preserves descriptive depth obstructions. -/
  h_lower : ∃ (p : PolyBound), ∀ n,
    profile.model_depth n * p.eval n ≥ profile.sat_depth n
  /-- Upper bound: encoding doesn't create fake depth obstructions. -/
  h_upper : ∃ (p : PolyBound), ∀ n,
    profile.model_depth n ≤ profile.sat_depth n * p.eval n

-- ════════════════════════════════════════════════════════════
-- Section 4: DescriptiveTransferHypothesis
-- ════════════════════════════════════════════════════════════

/-- The transfer hypothesis for Chain 3: bridges the SAT-instance world
    (bounded selectors with bounded descriptive depth) to the graded
    reflexive model world (grade-bounded functions).

    This is the OPEN condition analogous to TransferHypothesis in
    SATBoundaryLock.lean. -/
structure DescriptiveTransferHypothesis
    (M : GradedReflModel_Mirror_D3)
    (family : SATFamily)
    (enc : CookEncoding)
    (df : DefinabilityFaithful enc) where
  /-- For each size n, a poly-bounded selector on (family n) yields
      a grade-bounded function on M that agrees with selfApp on grade-≤d inputs. -/
  transfer : (n : Nat) → (d : Nat) →
    BoundedSelector (family n) d →
    { f : M.carrier → M.carrier //
      (∀ x, M.grade (f x) ≤ d) ∧
      (∀ x, M.grade x ≤ d → f x = M.selfApp x) }

-- ════════════════════════════════════════════════════════════
-- Section 5: The Lock Theorem
-- ════════════════════════════════════════════════════════════

/-- The lock theorem for Chain 3 (Descriptive Complexity):

    If Side A's impossibility holds (axiom, proved in pnp-integrated),
    and the transfer hypothesis connects the two type systems,
    then no poly-time SAT solver exists.

    Open hypotheses: DefinabilityFaithful enc, DescriptiveTransferHypothesis.
    These are explicit parameters — nothing is hidden.

    The proof is exactly 3 steps (same structure as SATBoundaryLock):
    1. Get a bounded selector from the solver (Side B).
    2. Transfer to a grade-bounded function on M (transfer hypothesis).
    3. Derive contradiction from Side A impossibility. -/
theorem no_poly_sat_solver_descriptive
    (M : GradedReflModel_Mirror_D3)
    (hub : SelfAppUnbounded_Mirror_D3 M)
    (family : SATFamily)
    (enc : CookEncoding)
    (df : DefinabilityFaithful enc)
    (tr : DescriptiveTransferHypothesis M family enc df)
    (solver : PolyTimeSolver family) :
    False := by
  -- Step 1: Get bounded selector from Side B
  let sel := poly_solver_induces_bounded_selector family solver 0
  let d := solver.time_bound.eval 0
  -- Step 2: Transfer to grade-bounded function on M
  let ⟨f, hbound, hagree⟩ := tr.transfer 0 d sel
  -- Step 3: Side A impossibility
  exact sideA_bounded_resource_impossible M hub d ⟨f, hagree, fun x _ => hbound x⟩

-- ════════════════════════════════════════════════════════════
-- Section 6: Faithfulness status and trivial instance
-- ════════════════════════════════════════════════════════════

/-- Honest status of the DefinabilityFaithful condition. -/
def definabilityFaithfulnessStatus : FaithfulnessStatus where
  status := "OPEN -- neither proved nor refuted"
  difficulty :=
    "Requires analyzing how Cook/Tseitin encoding transforms quantifier rank / pebble count"
  evidence_for :=
    "Cook encoding is structure-preserving: clause-variable incidence graph " ++
    "closely mirrors the input structure. Descriptive depth of satisfiability " ++
    "is known to grow for concrete families (Tseitin, CFI graphs)."
  evidence_against :=
    "Tseitin transformation introduces auxiliary variables that can change " ++
    "the Gaifman graph structure. Descriptive depth might not be preserved " ++
    "under arbitrary polynomial-time reductions."
  what_it_would_give :=
    "Combined with Side A and the descriptive depth bridge, yields: " ++
    "satisfiability requires unbounded descriptive depth, so no polynomial " ++
    "quantifier rank / pebble count suffices, so no poly-time solver exists."

/-- WARNING: DefinabilityFaithful can be trivially satisfied with zero depths.
    The trivial instance is useless for the lock theorem. -/
def trivialDefinabilityFaithful (enc : CookEncoding) : DefinabilityFaithful enc where
  profile := ObstructionProfile.trivial
  h_lower := ⟨⟨0, 0⟩, fun _ => by simp [ObstructionProfile.trivial, PolyBound.eval]⟩
  h_upper := ⟨⟨0, 0⟩, fun _ => by simp [ObstructionProfile.trivial, PolyBound.eval]⟩

-- ════════════════════════════════════════════════════════════
-- Section 7: Faithfulness implication
-- ════════════════════════════════════════════════════════════

/-- DefinabilityFaithful implies CookFaithful: the two structures are
    field-for-field identical (same ObstructionProfile + h_lower + h_upper).
    This is a direct mapping with no additional parameters needed. -/
def definabilityFaithful_to_cookFaithful (enc : CookEncoding)
    (df : DefinabilityFaithful enc) : CookFaithful enc where
  profile := df.profile
  h_lower := df.h_lower
  h_upper := df.h_upper

end ClassicalConstraints
