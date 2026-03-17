/-
  ClassicalConstraints/ProofComplexityModelConcrete.lean
  Concrete protocol lemmas completing the Chain 2 bridge.

  The dt_to_proto infrastructure (added to LiftingCore.lean) provides
  the concrete operations that map to ProofComplexityModelData fields:

  | ProofComplexityModelData field | Concrete lemma (proved)               | File          |
  |-------------------------------|---------------------------------------|---------------|
  | red                           | dt_to_proto ∘ proto_to_dt (flatten)   | LiftingCore   |
  | red_grade_le                  | proto_to_dt_to_proto_depth_le         | LiftingCore   |
  | red_idempotent                | dt_to_proto_roundtrip_idempotent      | LiftingCore   |
  | selfApp_eq_red                | by construction (selfApp IS flatten)  | this file     |

  The abstract bridge chain2_proofcomplexity_bridge already proves:
  for ANY M + SelfAppUnbounded + ProofComplexityModelData, False.
  These concrete lemmas show the four fields are satisfiable by real
  ProtocolTree/DecisionTree operations.

  WHY NO CONCRETE GRM: GradedReflModel_Mirror requires a roundtrip
  axiom fold(unfold(x)) = x. The flatten operation (dt_to_proto ∘ proto_to_dt)
  converts bob_sends nodes to alice_sends nodes — structurally different
  from the original, even though evaluation-equivalent at same-inputs
  (proto_to_dt_to_proto_eval). This information loss means no fold can
  recover the original protocol. This is the same structural reason as
  Chain 5: partial Lambek exists because full Lambek requires invertibility
  that projection-based selfApp cannot provide.

  STATUS: 0 sorry. Classical.choice allowed (Side B).
-/

import ClassicalConstraints.Chain2_ProofComplexity.ProofComplexityPartialLambek
import ClassicalConstraints.Chain2_ProofComplexity.LiftingCore

namespace ClassicalConstraints

-- ============================================================
-- Concrete field verification
-- ============================================================

/-- The flatten operation (dt_to_proto ∘ proto_to_dt) does not increase depth. -/
example (n : Nat) (p : ProtocolTree n n Bool) :
    (dt_to_proto (proto_to_dt p)).depth ≤ p.depth :=
  proto_to_dt_to_proto_depth_le p

/-- The flatten operation is idempotent. -/
example (n : Nat) (p : ProtocolTree n n Bool) :
    dt_to_proto (proto_to_dt (dt_to_proto (proto_to_dt p))) =
    dt_to_proto (proto_to_dt p) :=
  dt_to_proto_roundtrip_idempotent p

/-- The flatten roundtrip preserves evaluation at same-inputs. -/
example (n : Nat) (p : ProtocolTree n n Bool) (x : Fin n → Bool) :
    (dt_to_proto (proto_to_dt p)).eval x x = p.eval x x :=
  proto_to_dt_to_proto_eval p x

/-- proto_to_dt ∘ dt_to_proto = id on DecisionTree (the DT-side roundtrip). -/
example (n : Nat) (t : DecisionTree n) :
    proto_to_dt (dt_to_proto t) = t :=
  dt_to_proto_to_dt t

end ClassicalConstraints
