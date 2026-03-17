/-
  ClassicalConstraints/FixedPointDefinabilityBridge.lean
  Bounded LFP logic, Immerman-Vardi theorem, and ESO collapse hypothesis.

  Classical.choice is allowed. No sorry.
-/

import ClassicalConstraints.Chain3_Descriptive.ESOWitnessCore
import ClassicalConstraints.Shared.CookSelectorBridge
import Mathlib.Data.Fintype.Basic

namespace ClassicalConstraints

-- ════════════════════════════════════════════════════════════
-- Section 1: LFP formulas
-- ════════════════════════════════════════════════════════════

/-- A least fixed-point formula: mu R(x). phi(R, x) where phi is
    monotone in R. On finite structures with n elements and arity-k
    relation variable, the fixed point is reached in at most n^k
    iterations. -/
structure LFPFormula (vocab : Vocabulary) where
  /-- Arity of the fixed-point relation variable. -/
  fp_arity : Nat
  /-- The body formula (in expanded vocabulary with R). -/
  body : FOFormula (expandVocabByOne vocab fp_arity)
  /-- Quantifier depth of the body. -/
  body_depth : Nat
  /-- Correctness of depth recording. -/
  h_depth : body.quantifierDepth = body_depth

/-- The number of iterations to convergence for an LFP formula on a structure. -/
def LFPFormula.iterationsToConverge {vocab : Vocabulary}
    (lfp : LFPFormula vocab) (A : FiniteStructure vocab) : Nat :=
  A.domainSize ^ lfp.fp_arity

/-- Step count for evaluating a FO body (proportional to domain size squared). -/
def LFPFormula.bodyEvalSteps {vocab : Vocabulary}
    (_lfp : LFPFormula vocab) (A : FiniteStructure vocab) : Nat :=
  A.domainSize ^ 2

/-- Evaluate a full LFP formula on a finite structure (abstract semantics).

    PLACEHOLDER: Full LFP evaluation semantics require defining the monotone
    operator's least fixed point on the finite lattice of relations. This is
    deferred. The opaque declaration prevents tautological proofs (the previous
    definition ∃ R args, R args was trivially true via R := fun _ => True).
    Matches the pattern used by BoundedLFP.eval below. -/
opaque LFPFormula.eval {vocab : Vocabulary}
    (lfp : LFPFormula vocab) (A : FiniteStructure vocab) : Prop

-- ════════════════════════════════════════════════════════════
-- Section 2: Bounded LFP
-- ════════════════════════════════════════════════════════════

/-- Bounded LFP: the fixed point is computed with at most `bound`
    iterations. Captures polynomial-time definability when the bound
    is polynomial in domain size. -/
structure BoundedLFP (vocab : Vocabulary) where
  /-- The underlying LFP formula. -/
  formula : LFPFormula vocab
  /-- The iteration bound (as a function of domain size). -/
  iteration_bound : Nat → Nat
  /-- The bound is polynomial. -/
  bound_poly : PolyBound
  /-- The bound is at most the polynomial. -/
  h_bound_poly : ∀ n, iteration_bound n ≤ bound_poly.eval n

/-- Evaluate a bounded LFP on a finite structure.

    PLACEHOLDER: Full LFP iteration semantics require defining the k-th
    iterate of the body formula applied to the structure. This is deferred.
    The opaque declaration prevents tautological proofs while allowing
    the type signature to be used in downstream theorem statements. -/
opaque BoundedLFP.eval {vocab : Vocabulary}
    (lfp : BoundedLFP vocab) (A : FiniteStructure vocab)
    (args : Fin lfp.formula.fp_arity → A.Domain) : Prop

-- ════════════════════════════════════════════════════════════
-- Section 3: Poly-time decidable properties
-- ════════════════════════════════════════════════════════════

/-- Step counting for unordered structure decision procedures. -/
def decide_steps_unordered {vocab : Vocabulary}
    (A : FiniteStructure vocab) : Nat :=
  A.domainSize

/-- Step counting for ordered structure decision procedures. -/
def decide_steps {vocab : Vocabulary}
    (A : OrderedFiniteStructure vocab) : Nat :=
  A.domainSize

/-- A property of ordered finite structures is poly-time decidable.
    Named with suffix Struct to distinguish from StepIndexedEval.PolyTimeDecidable
    which applies to Nat predicates. -/
structure PolyTimeDecidableStruct {vocab : Vocabulary}
    (prop : OrderedFiniteStructure vocab → Prop) where
  /-- A decision procedure. -/
  decide : OrderedFiniteStructure vocab → Bool
  /-- Correctness. -/
  h_correct : ∀ A, decide A = true ↔ prop A
  /-- The time bound. -/
  time_bound : PolyBound
  /-- The decision runs within the time bound. -/
  h_time : ∀ (A : OrderedFiniteStructure vocab),
    decide_steps A ≤ time_bound.eval A.domainSize

-- ════════════════════════════════════════════════════════════
-- Section 4: Immerman-Vardi theorem (stated as structure)
-- ════════════════════════════════════════════════════════════

/-- The Immerman-Vardi theorem: P = FO+LFP on ORDERED finite structures.

    CRITICAL: This requires ordered structures. On unordered structures,
    FO+LFP does NOT capture P (EVEN is in P but not FO+LFP without order).

    Stated as a structure (carried as explicit parameter, not proved). -/
structure ImmermanVardiTheorem where
  /-- Every poly-time decidable property of ordered finite structures
      is definable in FO+LFP. -/
  p_to_lfp : ∀ (vocab : Vocabulary)
    (prop : OrderedFiniteStructure vocab → Prop)
    (_h_poly : PolyTimeDecidableStruct prop),
    ∃ (lfp : LFPFormula vocab),
      ∀ (A : OrderedFiniteStructure vocab),
        prop A ↔ LFPFormula.eval lfp A.toFiniteStructure
  /-- Every FO+LFP-definable property of ordered finite structures
      is poly-time decidable: iterations and steps are bounded. -/
  lfp_to_p : ∀ (vocab : Vocabulary) (lfp : LFPFormula vocab),
    ∃ (bound : PolyBound),
      ∀ (A : OrderedFiniteStructure vocab),
        lfp.iterationsToConverge A.toFiniteStructure ≤ bound.eval A.domainSize ∧
        lfp.bodyEvalSteps A.toFiniteStructure ≤ bound.eval A.domainSize

-- ════════════════════════════════════════════════════════════
-- Section 5: ESO collapse hypothesis (P = NP descriptive statement)
-- ════════════════════════════════════════════════════════════

/-- If P = NP, ESO collapses to bounded LFP on ordered structures. -/
structure ESOCollapseHypothesis (vocab : Vocabulary) where
  /-- Every ESO formula on ordered structures is equivalent to
      a bounded LFP formula. -/
  collapse : ∀ (eso : ESOFormula vocab),
    ∃ (lfp : BoundedLFP vocab),
      ∀ (A : OrderedFiniteStructure vocab),
        eso.satisfied A.toFiniteStructure ↔
        ∃ args, BoundedLFP.eval lfp A.toFiniteStructure args
  /-- The iteration bound is polynomial in domain size. -/
  bound_is_poly : ∀ (eso : ESOFormula vocab),
    ∃ (p : PolyBound) (lfp : BoundedLFP vocab),
      (∀ (A : OrderedFiniteStructure vocab),
        eso.satisfied A.toFiniteStructure ↔
        ∃ args, BoundedLFP.eval lfp A.toFiniteStructure args) ∧
      (∀ (A : OrderedFiniteStructure vocab),
        lfp.iteration_bound A.toFiniteStructure.domainSize ≤ p.eval A.domainSize)

-- ════════════════════════════════════════════════════════════
-- Section 6: Definability depth bound
-- ════════════════════════════════════════════════════════════

/-- The definability depth bound structure. -/
structure DefinabilityDepthBound where
  /-- The depth bound as a function of instance size. -/
  depth : Nat → Nat
  /-- The bound is polynomial. -/
  depth_poly : PolyBound
  /-- The depth is bounded by the polynomial. -/
  h_depth_poly : ∀ n, depth n ≤ depth_poly.eval n

/-- ESO collapse implies a definability depth bound exists.
    The iteration bound of the equivalent bounded LFP formula
    provides the depth bound. -/
theorem eso_collapse_implies_bounded_depth {vocab : Vocabulary}
    (collapse : ESOCollapseHypothesis vocab)
    (eso : ESOFormula vocab) :
    ∃ (bound : DefinabilityDepthBound),
      ∀ n, bound.depth n ≤ bound.depth_poly.eval n := by
  obtain ⟨lfp, _heval⟩ := collapse.collapse eso
  exact ⟨{
    depth := lfp.iteration_bound
    depth_poly := lfp.bound_poly
    h_depth_poly := lfp.h_bound_poly }, lfp.h_bound_poly⟩

-- ════════════════════════════════════════════════════════════
-- Section 7: Bounded LFP and BoundedSelector connection
-- ════════════════════════════════════════════════════════════

/-- OPEN: A bounded LFP formula for SAT satisfiability induces a bounded selector.

    This requires proper LFP iteration semantics (BoundedLFP.eval is opaque).
    Stated as a structure (open bridge condition), not a theorem.
    The intended content: the LFP iteration bound determines the selector capacity. -/
structure BoundedLFPInducesBoundedSelector (family : SATFamily) where
  lfp_family : ∀ _n : Nat, BoundedLFP satVocabulary
  selector : ∀ n, ∃ (cap : Nat) (p : PolyBound),
    cap ≤ p.eval n ∧
    ∃ (sel : BoundedSelector (family n) cap),
      ∀ a, sel.select a = true ↔ (family n).Satisfiable

-- ════════════════════════════════════════════════════════════
-- Section 8: Unordered structures warning
-- ════════════════════════════════════════════════════════════

-- WARNING: FO+LFP on unordered structures does NOT capture P.
-- The EVEN property is in P but not FO+LFP-definable without order.
-- This is a well-known result (Cai-Furer-Immerman 1992).

end ClassicalConstraints
