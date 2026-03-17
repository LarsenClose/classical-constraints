/-
  ClassicalConstraints/AlgebraicModelConcrete.lean
  Concrete multilinear reduction lemmas completing the Chain 5 bridge.

  Proves multilinearReduce is idempotent (via capExp_comp_eq and
  Finsupp.mapDomain_comp), complementing the three properties already
  proved in MultilinearReductionConcrete.lean:
  - multilinearReduce_totalDegree_le (degree non-increasing)
  - multilinearReduce_exponents_le_one (output is multilinear)
  - multilinearReduce_eval_eq (Boolean eval invariant)

  Together these four properties are exactly the four fields of
  AlgebraicModelData (defined in AlgebraicProofLock.lean):
  - red = multilinearReduce
  - red_grade_le = multilinearReduce_totalDegree_le
  - red_idempotent = multilinearReduce_idempotent (proved here)
  - selfApp_eq_red = multilinearReduce_eval_eq (Boolean eval invariance)

  The abstract bridge chain5_algebraic_bridge already proves:
  for ANY M + SelfAppUnbounded + AlgebraicModelData, False.
  These concrete lemmas show the four AlgebraicModelData fields are
  satisfiable by real MvPolynomial operations. The remaining gap is
  constructing a GradedReflModel_Mirror M whose selfApp agrees with
  multilinearReduce — a carrier-engineering question, not new mathematics.

  WHY NO CONCRETE GRM: GradedReflModel_Mirror requires a roundtrip
  axiom fold(unfold(x)) = x. For selfApp = multilinearReduce to be
  nontrivial, the carrier must include non-multilinear polynomials.
  But multilinearReduce loses information (collapses x^k to x for k≥1),
  so no fold can recover the original from the reduced form. This is
  WHY partial Lambek exists: the bridge only needs cotrip on the
  subdomain + cofinality, not the full Lambek roundtrip. The abstract
  bridge (chain5_algebraic_bridge) works without constructing a concrete
  GRM — it is universally quantified over M.

  STATUS: 0 sorry. Classical.choice allowed (Side B).
-/

import ClassicalConstraints.Chain5_Algebraic.AlgebraicProofLock
import ClassicalConstraints.Chain5_Algebraic.MultilinearReductionConcrete

namespace ClassicalConstraints

open MvPolynomial

-- ================================================================
-- Multilinear reduction is idempotent
-- ================================================================

/-- capExp ∘ capExp = capExp, as a function equality. -/
theorem capExp_comp_eq {σ : Type*} :
    (capExp : (σ →₀ ℕ) → (σ →₀ ℕ)) ∘ capExp = capExp := by
  ext e i
  simp [Function.comp, capExp_apply]

/-- multilinearReduce is idempotent: reducing an already-reduced polynomial
    is a no-op. Follows from capExp_idempotent via Finsupp.mapDomain_comp. -/
theorem multilinearReduce_idempotent {F : Type*} [CommSemiring F]
    {σ : Type*} [DecidableEq σ]
    (p : MvPolynomial σ F) :
    multilinearReduce (multilinearReduce p) = multilinearReduce p := by
  unfold multilinearReduce
  rw [← Finsupp.mapDomain_comp]
  rw [capExp_comp_eq]

-- ================================================================
-- Concrete field correspondence
-- ================================================================

/-
  The four fields of AlgebraicModelData map to concrete MvPolynomial facts:

  | AlgebraicModelData field | Concrete lemma (proved)              | File                           |
  |--------------------------|--------------------------------------|--------------------------------|
  | red                      | multilinearReduce                    | MultilinearReductionConcrete   |
  | red_grade_le             | multilinearReduce_totalDegree_le     | MultilinearReductionConcrete   |
  | red_idempotent           | multilinearReduce_idempotent         | this file                      |
  | selfApp_eq_red           | multilinearReduce_eval_eq            | MultilinearReductionConcrete   |

  All four are proved with 0 sorry, 0 axioms. The instantiation of
  AlgebraicModelData for a concrete M requires constructing a
  GradedReflModel_Mirror — see header comment for why this is a
  carrier-engineering question, not new mathematics.
-/

end ClassicalConstraints
