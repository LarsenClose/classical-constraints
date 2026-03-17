/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

ClassicalConstraints/ConcreteEncodings/CapabilityDelegationEncoding.lean

Candidate 2: Capability delegation encoding.
Uses the CapabilityWitnessInstance's delegation depth as the grade,
encoding SAT instances as capability chains of corresponding depth.

This encoding is structurally richer than the direct variable encoding
because delegation depth has built-in transport overhead (exactly 1 per
step), which provides a natural grade function with monotonic behavior.

STATUS: 0 sorry, 0 Classical.choice.
-/

import ClassicalConstraints.Shared.CookFaithfulness
import ClassicalConstraints.Chain7_Protocol.CapabilityWitnessInstance
import ClassicalConstraints.Chain7_Protocol.ProtocolWitnessFamilyLock

namespace ClassicalConstraints.ConcreteEncodings

-- ============================================================
-- Section 1: The capability delegation encoding
-- ============================================================

/-- The capability delegation encoding: carrier is Capability,
    grade is delegation depth, encode maps size n to a capability
    at depth n. -/
def capabilityDelegationEncoding : CookEncoding where
  Carrier := Capability
  grade := Capability.depth
  encode := fun n => ⟨0, "sat_encoding", n, true⟩
  grade_poly := ⟨1, 0⟩
  h_poly := fun n => by simp [PolyBound.eval]

/-- The grade of the encoded capability is exactly n. -/
theorem capability_grade_exact (n : Nat) :
    capabilityDelegationEncoding.grade (capabilityDelegationEncoding.encode n) = n := rfl

-- ============================================================
-- Section 2: CookFaithful with linear depth functions
-- ============================================================

/-- Linear obstruction profile: sat_depth = model_depth = id. -/
def capabilityLinearProfile : ObstructionProfile where
  sat_depth := fun n => n
  model_depth := fun n => n

/-- CookFaithful for the capability encoding with linear profiles. -/
def capability_cookFaithful :
    CookFaithful capabilityDelegationEncoding where
  profile := capabilityLinearProfile
  h_lower := ⟨⟨0, 1⟩, fun n => by
    simp [capabilityLinearProfile, PolyBound.eval]; omega⟩
  h_upper := ⟨⟨0, 1⟩, fun n => by
    simp [capabilityLinearProfile, PolyBound.eval]; omega⟩

-- ============================================================
-- Section 3: ConsequenceFaithful — where it works
-- ============================================================

/-- ConsequenceFaithful for the capability encoding with equal depths.
    h_consequence is id <= d -> id <= d, which is trivial. -/
def capability_consequenceFaithful_equal :
    ConsequenceFaithful capabilityDelegationEncoding where
  profile := capabilityLinearProfile
  h_lower := ⟨⟨0, 1⟩, fun n => by
    simp [capabilityLinearProfile, PolyBound.eval]; omega⟩
  h_upper := ⟨⟨0, 1⟩, fun n => by
    simp [capabilityLinearProfile, PolyBound.eval]; omega⟩
  h_consequence := fun _ _ h => h

-- ============================================================
-- Section 4: ConsequenceFaithful with transport-derived profiles
-- ============================================================

/- When model_depth tracks delegation chain length and sat_depth tracks
   the original variable count, consequence closure requires
   sat_depth n <= model_depth n pointwise. The delegation system's
   transport overhead of exactly 1 means depth grows linearly. -/

/-- ConsequenceFaithful from overhead: when sat_depth n <= n for all n
    and sat_depth is positive on positive inputs, the capability encoding
    is consequence-faithful with model_depth = id. -/
def capability_consequence_from_overhead
    (sat_depth : Nat -> Nat)
    (h_bounded : forall n, sat_depth n ≤ n)
    (h_positive : forall n, 0 < n -> 0 < sat_depth n) :
    ConsequenceFaithful capabilityDelegationEncoding :=
  { profile := ⟨sat_depth, fun n => n⟩
    h_lower := ⟨⟨0, 1⟩, fun n => by
      simp [PolyBound.eval]
      have := h_bounded n
      omega⟩
    h_upper := ⟨⟨1, 0⟩, fun n => by
      simp [PolyBound.eval]
      by_cases hn : n = 0
      · simp [hn]
      · have hpos := h_positive n (Nat.pos_of_ne_zero hn)
        exact Nat.le_mul_of_pos_left n hpos⟩
    h_consequence := fun n d hmd =>
      Nat.le_trans (h_bounded n) hmd }

-- ============================================================
-- Section 5: Transfer type analysis for capability encoding
-- ============================================================

/- For the capability encoding, the transfer needs to convert a
   BoundedSelector (on SAT assignments) into a grade-bounded function
   on M.carrier that agrees with selfApp.

   The capability system provides additional structure:
   1. Transport has overhead exactly 1 (transport_depth_increment)
   2. Transport collapse fails (capability_no_transport_collapse)
   3. Value collapse fails (capability_no_value_collapse)

   Properties 2 and 3 mirror Side A: selfApp being unbounded is
   analogous to transport collapse being impossible.

   However, the transfer still requires a dictionary between
   BoundedSelector (Boolean functions on assignments) and
   grade-bounded functions on M.carrier.

   KEY INSIGHT: Each delegation step costs 1 in grade. A BoundedSelector
   with capacity d observes d variables. If observing d variables could
   map to d delegation steps, the transfer would follow. But this
   mapping requires each variable observation to correspond to one
   delegation step, which is the HARD part. -/

/-- What the transfer would need for the capability encoding. -/
structure CapabilityTransferRequirements
    (M : GradedReflModel_Mirror)
    (family : SATFamily) where
  /-- Map each variable observation to a delegation step in the model. -/
  var_to_delegation : (n : Nat) → (v : Fin (family n).num_vars) →
    (M.carrier → M.carrier)
  /-- Each variable observation is grade-bounded by 1 (one step). -/
  h_var_bounded : ∀ n (v : Fin (family n).num_vars) x,
    M.grade (var_to_delegation n v x) ≤ M.grade x + 1
  /-- Composing d variable observations agrees with selfApp on
      grade-bounded inputs. This is where the hard content lies. -/
  h_composition_agrees : ∀ n d
    (vars : List (Fin (family n).num_vars))
    (_ : vars.length ≤ d),
    ∀ x, M.grade x ≤ d →
      M.grade x + vars.length ≤ d →
      True  -- placeholder: full condition requires defining the
            -- composition and proving agreement with selfApp

-- ============================================================
-- Section 6: Structural comparison with direct encoding
-- ============================================================

/- The capability encoding has the same ConsequenceFaithful properties
   as the direct encoding (both achieve it trivially with equal depths),
   but provides MORE STRUCTURE for the transfer:

   1. Natural grade increment: each delegation step adds exactly 1.
   2. Transport overhead bound: delegating k times costs k in grade.
   3. No transport collapse: delegation always increases depth.
   4. No value collapse: grade alone does not determine realizability.

   Despite these advantages, the GAP between BoundedSelector (Boolean
   functions on variable assignments) and grade-bounded model functions
   remains. The capability structure provides a natural grade function
   but not a natural CORRESPONDENCE between SAT variables and model
   elements.

   CONCLUSION: The capability encoding is structurally richer than the
   direct encoding but still insufficient for the transfer. The missing
   piece is COMPOSITIONAL structure: a way to build the dictionary
   incrementally, one variable at a time. -/

/-- The capability encoding achieves ConsequenceFaithful easily. -/
def capability_encoding_summary :
    ConsequenceFaithful capabilityDelegationEncoding :=
  capability_consequenceFaithful_equal

end ClassicalConstraints.ConcreteEncodings
