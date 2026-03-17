/-
  ClassicalConstraints/DescriptiveDepthBridge.lean
  Bridge connecting descriptive complexity measures to BoundedSelector capacity.

  The three descriptive resources (ESO/NP, FO-width/pebble,
  FO quantifier-rank/locality, FO+LFP) are NOT one unified scalar depth measure.
  This file keeps them as SEPARATE bridge structures and only packages implication chains,
  not "all measures are polynomially related."

  Classical.choice is allowed. No sorry.
-/

import ClassicalConstraints.Chain3_Descriptive.ESOWitnessCore
import ClassicalConstraints.Chain3_Descriptive.FixedPointDefinabilityBridge
import ClassicalConstraints.Chain3_Descriptive.PebbleGameObstruction
import ClassicalConstraints.Chain3_Descriptive.LocalityBridge
import ClassicalConstraints.Shared.CookSelectorBridge

namespace ClassicalConstraints

-- ════════════════════════════════════════════════════════════
-- Section 1: Separate bridge structures (not bundled into one depth)
-- ════════════════════════════════════════════════════════════

/-- Bridge from selector capacity to FO quantifier rank.
    A bounded selector induces an FO formula with bounded quantifier depth.
    These are distinct resources; this bridge only goes in one direction. -/
structure SelectorToFOQuantifierBridge (phi : SATInstance) (capacity : Nat) where
  /-- Convert a bounded selector to an FO formula over the fixed SAT vocabulary. -/
  to_formula : BoundedSelector phi capacity → FOFormula satVocabulary
  /-- The formula has quantifier rank at most capacity. -/
  h_rank_bounded : ∀ (sel : BoundedSelector phi capacity),
    (to_formula sel).quantifierDepth ≤ capacity
  /-- The formula has at most capacity variables. -/
  h_width_bounded : ∀ (sel : BoundedSelector phi capacity),
    (to_formula sel).numVariables ≤ capacity
  /-- Correctness: the formula agrees with the selector on the fixed structure. -/
  h_correct : ∀ (sel : BoundedSelector phi capacity)
    (A : FiniteStructure satVocabulary)
    (a : Fin phi.num_vars → Bool),
    FOFormula.eval satVocabulary A (to_formula sel) ↔
      (sel.select a = true)

/-- Bridge from FO quantifier rank to selector capacity.
    An FO formula with quantifier depth q on ordered structures induces a selector.
    Only holds on ordered structures (Immerman-Vardi direction). -/
structure FOQuantifierToSelectorBridge (family : SATFamily) where
  /-- Quantifier rank bounds selector capacity polynomially. -/
  rank_bounds_capacity : ∀ (n : Nat) (q : Nat)
    (phi : FOFormula satVocabulary)
    (_h_rank : phi.quantifierDepth ≤ q),
    ∃ (capacity : Nat) (p : PolyBound),
      capacity ≤ p.eval q ∧
      ∃ (sel : BoundedSelector (family n) capacity),
        ∀ (a : Fin (family n).num_vars → Bool),
          sel.select a = true ↔
          FOFormula.eval satVocabulary (family n).toFixedStructure phi

/-- Bridge from pebble count (FO variable width) to FO formula non-definability.
    A k-pebble lower bound implies the property is not k-variable FO definable.
    Separate from quantifier rank. -/
structure PebbleToFOWidthBridge where
  /-- k-pebble lower bound blocks k-variable FO definition. -/
  pebble_blocks_width : ∀ (k : Nat) (fam : SATInstancePebbleFamily)
    (_pfe : PebbleFormulaEquivalence),
    ¬∃ (phi : FOFormula satVocabulary),
      phi.numVariables ≤ k ∧
      ∀ C, FOFormula.eval satVocabulary C phi ↔
           fam.target_property k C

/-- Bridge from Gaifman locality to selector capacity radius bound.
    FO quantifier rank controls Gaifman locality radius.
    Separate from variable width / pebble count. -/
structure GaifmanFromQuantifierBridge where
  /-- FO formula with depth q decomposes into local sentences with bounded radius. -/
  locality_from_rank : ∀ (q : Nat) (phi : FOFormula satVocabulary)
    (_h_depth : phi.quantifierDepth ≤ q),
    ∃ (local_sentences : List (GaifmanLocalSentence satVocabulary)),
      (∀ ls ∈ local_sentences, ls.radius ≤ locality_radius_bound q) ∧
      (∀ (A : FiniteStructure satVocabulary),
        FOFormula.eval satVocabulary A phi ↔
        boolean_combination_eval local_sentences A)

-- ════════════════════════════════════════════════════════════
-- Section 2: Descriptive depth profile (kept minimal)
-- ════════════════════════════════════════════════════════════

/-- The quantifier-rank profile of a SAT family: how deep an FO sentence
    is needed to define satisfiability at each size n.
    This is just the quantifier-rank resource — not bundled with pebble/LFP. -/
structure QuantifierRankProfile (family : SATFamily) where
  /-- Quantifier rank needed at each size. -/
  rank_at : Nat → Nat
  /-- The rank is always at least 1. -/
  h_growing : ∀ n, rank_at n ≥ 1

-- ════════════════════════════════════════════════════════════
-- Section 3: Core theorems
-- ════════════════════════════════════════════════════════════

/-- A poly-time solver implies bounded quantifier rank for satisfiability.
    This is the selector → FO formula direction only. -/
theorem poly_solver_implies_bounded_quantifier_rank
    (family : SATFamily)
    (solver : PolyTimeSolver family)
    (stf : ∀ n, SelectorToFOQuantifierBridge (family n) (solver.time_bound.eval n)) :
    ∃ (profile : QuantifierRankProfile family) (p : PolyBound),
      ∀ n, profile.rank_at n ≤ p.eval n := by
  -- Step 1: Solver gives bounded selector at each n
  have h_sel : ∀ n, BoundedSelector (family n) (solver.time_bound.eval n) :=
    poly_solver_induces_bounded_selector family solver
  -- Step 2: Bridge converts selector to FO formula with bounded quantifier rank
  -- The bridge's h_rank_bounded gives: rank ≤ capacity = solver.time_bound.eval n
  let profile : QuantifierRankProfile family := {
    rank_at := fun n => max 1 ((stf n).to_formula (h_sel n)).quantifierDepth
    h_growing := fun n => Nat.le_max_left 1 _ }
  refine ⟨profile, ⟨solver.time_bound.degree, solver.time_bound.constant + 1⟩, fun n => ?_⟩
  show max 1 ((stf n).to_formula (h_sel n)).quantifierDepth ≤
    PolyBound.eval ⟨solver.time_bound.degree, solver.time_bound.constant + 1⟩ n
  simp only [PolyBound.eval]
  -- The bridge gives: quantifierDepth ≤ capacity = solver.time_bound.eval n
  have h_rank := (stf n).h_rank_bounded (h_sel n)
  have : solver.time_bound.eval n = n ^ solver.time_bound.degree + solver.time_bound.constant :=
    rfl
  omega

/-- If the quantifier rank of satisfiability grows faster than any polynomial,
    then no poly-time solver exists. -/
theorem unbounded_rank_obstructs_solver
    (family : SATFamily)
    (h_unbounded : ∀ (p : PolyBound),
      ∃ n, ¬∃ (phi : FOFormula satVocabulary),
        phi.quantifierDepth ≤ p.eval n ∧
        ∀ A, FOFormula.eval satVocabulary A phi ↔
             (family n).Satisfiable)
    (solver : PolyTimeSolver family)
    (stf : ∀ n, SelectorToFOQuantifierBridge (family n) (solver.time_bound.eval n))
    (h_stf_correct : ∀ n A,
      FOFormula.eval satVocabulary A
        ((stf n).to_formula (poly_solver_induces_bounded_selector family solver n)) ↔
      (family n).Satisfiable) :
    False := by
  obtain ⟨n, h_no_formula⟩ := h_unbounded solver.time_bound
  apply h_no_formula
  exact ⟨(stf n).to_formula (poly_solver_induces_bounded_selector family solver n),
    (stf n).h_rank_bounded _,
    h_stf_correct n⟩

/-- A k-pebble lower bound (on a pebble family) implies the target property
    is not k-variable FO definable over the fixed SAT vocabulary.
    This uses the pebble → FO-width bridge directly. -/
theorem pebble_lower_bound_implies_variable_lower_bound
    (k : Nat)
    (fam : SATInstancePebbleFamily)
    (pfe : PebbleFormulaEquivalence) :
    ¬∃ (phi : FOFormula satVocabulary),
        phi.numVariables ≤ k ∧
        ∀ C, FOFormula.eval satVocabulary C phi ↔
             fam.target_property k C :=
  unbounded_pebble_requirement fam pfe k

/-- Gaifman locality radius is bounded by quantifier rank.
    Given a selector-to-formula bridge, the formula decomposes into local sentences
    with radius bounded by the selector capacity. -/
theorem capacity_bounds_locality_radius
    {phi : SATInstance} {c : Nat}
    (sel : BoundedSelector phi c)
    (gaifman : GaifmanLocality)
    (stf : SelectorToFOQuantifierBridge phi c) :
    ∃ (local_sentences : List (GaifmanLocalSentence satVocabulary)),
      (∀ ls ∈ local_sentences, ls.radius ≤ locality_radius_bound c) ∧
      (∀ (A : FiniteStructure satVocabulary),
        FOFormula.eval satVocabulary A (stf.to_formula sel) ↔
        boolean_combination_eval local_sentences A) := by
  obtain ⟨local_sents, h_radii, h_equiv⟩ :=
    gaifman.decomposition satVocabulary (stf.to_formula sel)
  refine ⟨local_sents, fun ls hls => ?_, fun A => h_equiv A⟩
  exact (h_radii ls hls).trans (locality_radius_bound_mono (stf.h_rank_bounded sel))

end ClassicalConstraints
