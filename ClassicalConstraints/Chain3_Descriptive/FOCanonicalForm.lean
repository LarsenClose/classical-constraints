/-
  ClassicalConstraints/FOCanonicalForm.lean
  Negation Normal Form (NNF) conversion for FOFormula.

  Defines foCanonical (NNF conversion via polarity-tracking helper) and
  proves three properties:
  1. foCanonical_depth_le: quantifier depth is preserved (actually equal)
  2. foCanonical_idempotent: foCanonical (foCanonical phi) = foCanonical phi
  3. (eval preservation documented but requires full evalWithVal infrastructure)

  These are the concrete operations corresponding to
  DescriptiveComplexityModelData fields (Chain 3 partial Lambek bridge):
  - red = foCanonical
  - red_grade_le = foCanonical_depth_le
  - red_idempotent = foCanonical_idempotent

  STATUS: 0 sorry. Classical.choice allowed (Side B).
-/

import ClassicalConstraints.Chain3_Descriptive.ESOWitnessCore

namespace ClassicalConstraints

-- ============================================================
-- NNF conversion with polarity tracking
-- ============================================================

/-- NNF conversion with polarity tracking. Positive polarity normalizes
    directly; negative polarity pushes negation inward via De Morgan.
    Structural recursion on the FOFormula argument. -/
def foCanonicalAux {vocab : Vocabulary} : Bool → FOFormula vocab → FOFormula vocab
  | true,  .feq i j     => .feq i j
  | false, .feq i j     => .fneg (.feq i j)
  | true,  .frel i args => .frel i args
  | false, .frel i args => .fneg (.frel i args)
  | true,  .fneg φ      => foCanonicalAux false φ
  | false, .fneg φ      => foCanonicalAux true φ
  | true,  .fconj φ ψ  => .fconj (foCanonicalAux true φ) (foCanonicalAux true ψ)
  | false, .fconj φ ψ  => .fdisj (foCanonicalAux false φ) (foCanonicalAux false ψ)
  | true,  .fdisj φ ψ  => .fdisj (foCanonicalAux true φ) (foCanonicalAux true ψ)
  | false, .fdisj φ ψ  => .fconj (foCanonicalAux false φ) (foCanonicalAux false ψ)
  | true,  .fex φ       => .fex (foCanonicalAux true φ)
  | false, .fex φ       => .fall (foCanonicalAux false φ)
  | true,  .fall φ      => .fall (foCanonicalAux true φ)
  | false, .fall φ      => .fex (foCanonicalAux false φ)

/-- Canonical form of an FO formula: NNF conversion (positive polarity). -/
def foCanonical {vocab : Vocabulary} (φ : FOFormula vocab) : FOFormula vocab :=
  foCanonicalAux true φ

-- ============================================================
-- Depth preservation
-- ============================================================

/-- NNF conversion preserves quantifier depth for any polarity. -/
theorem foCanonicalAux_depth {vocab : Vocabulary} (q : Bool) (φ : FOFormula vocab) :
    (foCanonicalAux q φ).quantifierDepth = φ.quantifierDepth := by
  induction φ generalizing q with
  | feq i j => cases q <;> simp [foCanonicalAux, FOFormula.quantifierDepth]
  | frel i args => cases q <;> simp [foCanonicalAux, FOFormula.quantifierDepth]
  | fneg φ ih =>
    cases q <;> simp only [foCanonicalAux, FOFormula.quantifierDepth] <;> exact ih _
  | fconj φ ψ ihφ ihψ =>
    cases q <;> simp [foCanonicalAux, FOFormula.quantifierDepth, ihφ, ihψ]
  | fdisj φ ψ ihφ ihψ =>
    cases q <;> simp [foCanonicalAux, FOFormula.quantifierDepth, ihφ, ihψ]
  | fex φ ih =>
    cases q <;> simp [foCanonicalAux, FOFormula.quantifierDepth, ih]
  | fall φ ih =>
    cases q <;> simp [foCanonicalAux, FOFormula.quantifierDepth, ih]

/-- NNF conversion preserves quantifier depth (inequality form for the interface). -/
theorem foCanonical_depth_le {vocab : Vocabulary} (φ : FOFormula vocab) :
    (foCanonical φ).quantifierDepth ≤ φ.quantifierDepth := by
  rw [foCanonical, foCanonicalAux_depth]

/-- NNF conversion preserves quantifier depth exactly. -/
theorem foCanonical_depth_eq {vocab : Vocabulary} (φ : FOFormula vocab) :
    (foCanonical φ).quantifierDepth = φ.quantifierDepth := by
  exact foCanonicalAux_depth true φ

-- ============================================================
-- Idempotence
-- ============================================================

/-- Key stability lemma: applying foCanonicalAux true to an already-normalized
    formula (under any polarity q) is the identity. This is the engine of
    idempotence: the output of foCanonicalAux is always in NNF (negations
    only at atoms), so a second pass with positive polarity is a no-op. -/
theorem foCanonicalAux_stable {vocab : Vocabulary} (q : Bool) (φ : FOFormula vocab) :
    foCanonicalAux true (foCanonicalAux q φ) = foCanonicalAux q φ := by
  induction φ generalizing q with
  | feq i j => cases q <;> simp [foCanonicalAux]
  | frel i args => cases q <;> simp [foCanonicalAux]
  | fneg φ ih =>
    cases q <;> simp only [foCanonicalAux] <;> exact ih _
  | fconj φ ψ ihφ ihψ =>
    cases q <;> simp only [foCanonicalAux]
    · -- q = false: output is fdisj (De Morgan: ¬(φ ∧ ψ) → ¬φ ∨ ¬ψ)
      exact congr (congr_arg FOFormula.fdisj (ihφ false)) (ihψ false)
    · -- q = true: output is fconj
      exact congr (congr_arg FOFormula.fconj (ihφ true)) (ihψ true)
  | fdisj φ ψ ihφ ihψ =>
    cases q <;> simp only [foCanonicalAux]
    · -- q = false: output is fconj (De Morgan: ¬(φ ∨ ψ) → ¬φ ∧ ¬ψ)
      exact congr (congr_arg FOFormula.fconj (ihφ false)) (ihψ false)
    · -- q = true: output is fdisj
      exact congr (congr_arg FOFormula.fdisj (ihφ true)) (ihψ true)
  | fex φ ih =>
    cases q <;> simp only [foCanonicalAux]
    · exact congr_arg FOFormula.fall (ih false)
    · exact congr_arg FOFormula.fex (ih true)
  | fall φ ih =>
    cases q <;> simp only [foCanonicalAux]
    · exact congr_arg FOFormula.fex (ih false)
    · exact congr_arg FOFormula.fall (ih true)

/-- NNF conversion is idempotent: normalizing an already-normal formula
    is the identity. -/
theorem foCanonical_idempotent {vocab : Vocabulary} (φ : FOFormula vocab) :
    foCanonical (foCanonical φ) = foCanonical φ := by
  exact foCanonicalAux_stable true φ

end ClassicalConstraints
