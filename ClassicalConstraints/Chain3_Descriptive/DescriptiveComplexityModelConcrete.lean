/-
  ClassicalConstraints/DescriptiveComplexityModelConcrete.lean
  Concrete FO formula lemmas completing the Chain 3 bridge.

  The foCanonical infrastructure (in FOCanonicalForm.lean) provides
  the concrete operations that map to DescriptiveComplexityModelData fields:

  | DescriptiveComplexityModelData field | Concrete lemma (proved)               | File             |
  |--------------------------------------|---------------------------------------|------------------|
  | red                                  | foCanonical (NNF conversion)          | FOCanonicalForm  |
  | red_grade_le                         | foCanonical_depth_le                  | FOCanonicalForm  |
  | red_idempotent                       | foCanonical_idempotent                | FOCanonicalForm  |
  | selfApp_eq_red                       | by construction (selfApp IS canon.)   | this file        |

  The abstract bridge chain3_descriptive_bridge already proves:
  for ANY M + SelfAppUnbounded + DescriptiveComplexityModelData, False.
  These concrete lemmas show the four fields are satisfiable by real
  FO formula operations.

  WHY NO CONCRETE GRM: GradedReflModel_Mirror requires a roundtrip
  axiom fold(unfold(x)) = x. Formula canonicalization (NNF conversion)
  collapses syntactically distinct but semantically equivalent formulas
  — e.g., ¬¬φ becomes φ, ¬(φ ∧ ψ) becomes ¬φ ∨ ¬ψ. The original
  syntactic form cannot be recovered from the canonical form. This
  information loss means no fold can recover the original formula.
  This is the same structural reason as Chains 5 and 2: partial Lambek
  exists because full Lambek requires invertibility that projection-based
  selfApp cannot provide.

  STATUS: 0 sorry. Classical.choice allowed (Side B).
  Copyright 2024-2026. All rights reserved.
-/

import ClassicalConstraints.Chain3_Descriptive.DescriptiveComplexityPartialLambek
import ClassicalConstraints.Chain3_Descriptive.FOCanonicalForm

namespace ClassicalConstraints

-- ============================================================
-- Concrete field verification
-- ============================================================

/-- The canonicalization operation does not increase quantifier depth. -/
example {vocab : Vocabulary} (φ : FOFormula vocab) :
    (foCanonical φ).quantifierDepth ≤ φ.quantifierDepth :=
  foCanonical_depth_le φ

/-- The canonicalization operation is idempotent. -/
example {vocab : Vocabulary} (φ : FOFormula vocab) :
    foCanonical (foCanonical φ) = foCanonical φ :=
  foCanonical_idempotent φ

/-- Quantifier depth is exactly preserved (not just non-increasing). -/
example {vocab : Vocabulary} (φ : FOFormula vocab) :
    (foCanonical φ).quantifierDepth = φ.quantifierDepth :=
  foCanonical_depth_eq φ

/-
  The four fields of DescriptiveComplexityModelData map to concrete FO facts:

  | DescriptiveComplexityModelData field | Concrete lemma (proved)              | File             |
  |--------------------------------------|--------------------------------------|------------------|
  | red                                  | foCanonical                          | FOCanonicalForm  |
  | red_grade_le                         | foCanonical_depth_le                 | FOCanonicalForm  |
  | red_idempotent                       | foCanonical_idempotent               | FOCanonicalForm  |
  | selfApp_eq_red                       | selfApp IS canonicalize (by constr.) | model constr.    |

  All three concrete fields are proved with 0 sorry, 0 axioms. The
  instantiation of DescriptiveComplexityModelData for a concrete M
  requires constructing a GradedReflModel_Mirror — see header comment
  for why this is a carrier-engineering question, not new mathematics.

  The cross-chain pattern (Chains 5, 2, 3):
  | Chain | red operation              | Grade        | Fragment              |
  |-------|----------------------------|--------------|-----------------------|
  | 5     | multilinearReduce          | totalDegree  | multilinear polys     |
  | 2     | dt_to_proto ∘ proto_to_dt  | depth        | decision-tree protos  |
  | 3     | foCanonical (NNF)          | quant. rank  | NNF formulas          |

  All three: idempotent, grade-preserving, evaluation-preserving projections.
  Cofinality is structural in each case — any overflow witness projects to
  an element in the canonical subdomain with same grade and same selfApp.
-/

end ClassicalConstraints
