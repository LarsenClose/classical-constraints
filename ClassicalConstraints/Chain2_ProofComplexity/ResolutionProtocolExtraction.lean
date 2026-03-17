/-
  ClassicalConstraints/ResolutionProtocolExtraction.lean
  Supplementary material for the resolution-to-protocol extraction.
  Imported by ClassicalConstraints.lean (barrel file).

  The theorem `short_proof_bounded_comm_trivial` in CommunicationProtocolBridge.lean
  provides a direct (vacuous) proof. This file provides the width-bounded variant
  and documents why both versions are vacuously true.

  The CommProtocol type only requires existence of a ProtocolTree computing
  SOME Boolean function — it does not constrain WHICH function the protocol
  computes. Since ProtocolTree.leaf has depth 0, a constant protocol always
  satisfies any upper bound on depth.

  The MEANINGFUL version (Krajíček extraction) would require the protocol
  to output a separating coordinate i where Alice's and Bob's inputs disagree,
  with the correctness condition from KWGame.correct. That requires enriching
  CommProtocol or using KWGame directly. See notes at the bottom.

  STATUS: 0 sorry. No Classical.choice beyond imports.
-/

import ClassicalConstraints.Chain2_ProofComplexity.CommunicationProtocolBridge

namespace ClassicalConstraints

-- ════════════════════════════════════════════════════════════
-- Width-bounded variant (strictly stronger than size-bounded)
-- ════════════════════════════════════════════════════════════

/-- Width-bounded version: depth ≤ ref.width. Strictly stronger than the
    size-bounded version since width ≤ size always holds. Same trivial
    proof applies: a constant protocol has depth 0 ≤ anything. -/
theorem resolution_to_protocol_width (φ : CNF)
    (ref : ResolutionRefutation φ) :
    ∃ proto : CommProtocol φ.num_vars φ.num_vars,
      proto.tree.depth ≤ ref.width :=
  ⟨⟨.leaf true, fun _ _ => true, fun _ _ => rfl⟩, Nat.zero_le _⟩

-- ════════════════════════════════════════════════════════════
-- Note on the meaningful version
-- ════════════════════════════════════════════════════════════

/-
  The Krajíček extraction theorem says something much stronger than what
  `short_proof_bounded_comm_trivial` asserts. The meaningful statement is:

  Given an unsatisfiable CNF φ over variables {x₁,...,xₙ} and a resolution
  refutation R, there exists a communication protocol P such that:
  1. P has depth ≤ width(R)
  2. For every pair of assignments (a, b) with a ≠ b, the protocol
     outputs a coordinate i where a(xᵢ) ≠ b(xᵢ) AND the clause at
     that point in the refutation is falsified by the combined assignment.

  This is the content of the KW-game theorem. To formalize it properly,
  CommProtocol would need to output `Fin n` (a separating coordinate)
  with a correctness condition, rather than just `Bool`. The existing
  `KWGame` structure has the right shape for this, but `short_proof_bounded_comm_trivial`
  was stated using `CommProtocol` (Bool output, no separation requirement),
  making it trivially provable.

  If the downstream chain needs the actual separation property in the future,
  the right fix is:
  1. Define a `KWProtocolFromRefutation` structure with the separation correctness
  2. Prove the Krajíček extraction into that structure
  3. Have downstream consumers use the enriched type
-/

end ClassicalConstraints
