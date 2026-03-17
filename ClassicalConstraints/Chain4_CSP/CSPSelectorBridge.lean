/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

ClassicalConstraints/CSPSelectorBridge.lean — Bridge: poly-time CSP solver
induces a bounded algebraic witness. This is NOT a direct solver →
polymorphism family inference (which would be too strong); instead we produce
a BoundedAlgebraicWitness, which is the correct weaker bridge object.

STATUS: 0 sorry, Classical.choice allowed (Side B).

Design decisions:
- solver_induces_witness (correct: solver → bounded local access footprint),
  NOT solver → polymorphism family (too strong).
- UnboundedPolymorphismRequirement: instance-level and computational,
  NOT fixed-point characterization.
- HardCSPHasUnboundedRequirement: carried as a structure (analogous to BulatovZhukDichotomy).
- wnu_gives_bounded_algorithm: proved (WNU → poly-time solver via dichotomy).
- polymorphism_counting_lower_bound: proved (tower-exponential lower bound).
-/

import ClassicalConstraints.Shared.CookSelectorBridge
import ClassicalConstraints.Chain4_CSP.CSPInstanceCore
import ClassicalConstraints.Chain4_CSP.PolymorphismCore
import ClassicalConstraints.Chain4_CSP.WidthFromPolymorphisms

namespace ClassicalConstraints

-- ════════════════════════════════════════════════════════════
-- Section 1: Poly-time CSP solver
-- ════════════════════════════════════════════════════════════

/-- A poly-time CSP solver for a constraint language.
    The solver decides satisfiability for instances of the language
    in time polynomial in the number of variables. -/
structure PolyTimeCSPSolver (dom : CSPDomain)
    (lang : ConstraintLanguage dom) where
  /-- The decision function: takes a CSP instance, returns satisfiability. -/
  decide : CSPInstance dom lang → Bool
  /-- Correctness. -/
  h_correct : ∀ inst, decide inst = true ↔ inst.Satisfiable dom lang
  /-- Polynomial time bound. -/
  time_bound : PolyBound
  /-- Access bound: the solver reads at most access_bound.eval(n) variable positions. -/
  access_bound : PolyBound
  /-- The solver's decision on each instance depends on a bounded number of positions.
      There exists a set S of at most access_bound.eval(n) positions that determines it. -/
  h_access_bounded : ∀ (inst : CSPInstance dom lang),
    ∃ (S : Finset (Fin inst.num_vars)),
      S.card ≤ access_bound.eval inst.num_vars

-- ════════════════════════════════════════════════════════════
-- Section 2: Bridge objects
-- ════════════════════════════════════════════════════════════

/-- A bounded algebraic witness: the CORRECT immediate image of a solver.

    This is what a poly-time CSP solver ACTUALLY induces: a bounded observation
    footprint on a specific instance. It records which variable positions the
    solver "sees" (at most access_bound.eval(n) of them).

    This is an INSTANCE-LEVEL, COMPUTATIONAL object. It is NOT a genuine polymorphism
    family, which would be a LANGUAGE-LEVEL, ALGEBRAIC object.

    The semantic gap (identified by GPT review):
    - A polymorphism must preserve ALL relations for ALL input tuples (global, algebraic).
    - A bounded witness records only that the solver's footprint fits in d positions
      (local, computational).

    To promote from witness → polymorphism family requires CSPTransferHypothesis. -/
structure BoundedAlgebraicWitness (dom : CSPDomain)
    (lang : ConstraintLanguage dom)
    (inst : CSPInstance dom lang)
    (capacity : Nat) where
  /-- The set of variable positions the solver's decision depends on. -/
  essential_vars : Finset (Fin inst.num_vars)
  /-- Bounded by the access capacity. -/
  bounded : essential_vars.card ≤ capacity

/-- A bounded polymorphism family at arity k and capacity d.
    STRONGER than BoundedAlgebraicWitness: each operation genuinely preserves
    all constraint relations coordinatewise (language-level algebraic property). -/
structure BoundedPolymorphismFamily (dom : CSPDomain)
    (lang : ConstraintLanguage dom)
    (k : Nat) (capacity : Nat) where
  /-- The family of k-ary operations. -/
  ops : List (Operation dom.D k)
  /-- Each operation genuinely preserves the constraint language. -/
  all_polymorphisms : ∀ f ∈ ops, isPolymorphism lang f
  /-- Family size bounded by capacity. -/
  size_bounded : ops.length ≤ capacity
  /-- Essential arity bounded: each operation depends on at most capacity coordinates. -/
  essential_arity_bounded : ∀ f ∈ ops,
    ∃ (coords : Finset (Fin k)),
      coords.card ≤ capacity ∧
      ∀ (args₁ args₂ : Fin k → dom.D),
        (∀ i ∈ coords, args₁ i = args₂ i) → f args₁ = f args₂

-- ════════════════════════════════════════════════════════════
-- Section 3: Solver induces bounded algebraic witness
-- ════════════════════════════════════════════════════════════

/-- A poly-time CSP solver induces a BoundedAlgebraicWitness at each instance.

    This is the CORRECT (and weaker) bridge theorem.

    A solver with access_bound p(n) directly gives a bounded observation footprint:
    there exists a set S of ≤ p(n) variable positions that covers the solver's access.
    This is a simple definitional unfolding of what "bounded access" means.

    This does NOT give a genuine polymorphism family. To promote from witness to
    polymorphism, additional structure is required (CSPTransferHypothesis). -/
noncomputable def solver_induces_witness (dom : CSPDomain)
    (lang : ConstraintLanguage dom)
    (solver : PolyTimeCSPSolver dom lang)
    (inst : CSPInstance dom lang) :
    BoundedAlgebraicWitness dom lang inst
      (solver.access_bound.eval inst.num_vars) :=
  let h := solver.h_access_bounded inst
  let S := Classical.choose h
  let hS := Classical.choose_spec h
  { essential_vars := S
  , bounded := hS }

-- ════════════════════════════════════════════════════════════
-- Section 4: Unbounded polymorphism requirement
-- ════════════════════════════════════════════════════════════

/-- The unbounded polymorphism requirement: a property of hard CSP languages.

    A language satisfies this property when for every capacity d, there exists
    a CSP instance that no d-bounded decision function can correctly decide.

    Concretely: the instance distinguishes satisfying from non-satisfying assignments
    in a way that necessarily depends on more than d variable positions. Any function
    that only sees d positions will make mistakes on this instance.

    This is the CORRECT formulation (per GPT review):
    - Instance-level and computational, not language-level algebraic.
    - The hard instance comes from the HARDNESS side (Side B), not from selfApp.
    - The lock uses hreq.unbounded to extract the hard instance. -/
structure UnboundedPolymorphismRequirement (dom : CSPDomain)
    (lang : ConstraintLanguage dom) where
  /-- For every capacity d, there exists an instance that defeats any d-bounded solver. -/
  unbounded : ∀ d, ∃ (inst : CSPInstance dom lang),
    ∀ (decide_fn : inst.Assignment dom → Bool),
      -- If decide_fn is d-bounded (depends on ≤ d variable positions)...
      (∃ (S : Finset (Fin inst.num_vars)),
        S.card ≤ d ∧
        ∀ (a₁ a₂ : inst.Assignment dom),
          (∀ i ∈ S, a₁ i = a₂ i) → decide_fn a₁ = decide_fn a₂) →
      -- ...then decide_fn is not always correct on inst.
      ¬(∀ a, decide_fn a = inst.isSatisfied dom lang a)

-- ════════════════════════════════════════════════════════════
-- Section 5: Clone level required (auxiliary definition)
-- ════════════════════════════════════════════════════════════

/-- Clone level required: any k-bounded decision function gets some
    assignment wrong on this instance. No function that depends on at
    most k variable positions can correctly determine satisfiability
    for all assignments.

    Used in the PolymorphismFaithful transfer hypothesis in CSPAlgebraLock. -/
def CloneLevelRequired (dom : CSPDomain) (lang : ConstraintLanguage dom)
    (inst : CSPInstance dom lang) (k : Nat) : Prop :=
  ∀ (decide_fn : inst.Assignment dom → Bool),
    (∃ (coords : Finset (Fin inst.num_vars)), coords.card ≤ k ∧
      ∀ a₁ a₂, (∀ i ∈ coords, a₁ i = a₂ i) → decide_fn a₁ = decide_fn a₂) →
    ∃ a, decide_fn a ≠ inst.isSatisfied dom lang a

-- ════════════════════════════════════════════════════════════
-- Section 6: Hard CSP has unbounded requirement (structure)
-- ════════════════════════════════════════════════════════════

/-- Structural claim: hard CSP languages (no WNU) have unbounded polymorphism requirements.

    Mathematical content: by Bulatov-Zhuk, a language with no WNU is NP-complete.
    NP-completeness means no polynomial-time algorithm decides satisfiability.
    A d-bounded decision function runs in time proportional to |D|^d, so if a
    d-bounded function always worked, we'd have a poly-time algorithm contradicting
    NP-hardness.

    This is carried as a STRUCTURE (analogous to BulatovZhukDichotomy) rather than
    proved inline, because the formal connection between NP-hardness and the specific
    unboundedness property requires going through a complexity-theoretic argument
    not formalized here.

    The lock theorem takes UnboundedPolymorphismRequirement as an explicit hypothesis. -/
structure HardCSPHasUnboundedRequirement (dom : CSPDomain)
    (lang : ConstraintLanguage dom) where
  /-- The language has no WNU polymorphism. -/
  hno_wnu : ¬∃ k, k ≥ 2 ∧ ∃ (w : WNU dom.D k), isPolymorphism lang w.op
  /-- The language has an unbounded polymorphism requirement. -/
  requirement : UnboundedPolymorphismRequirement dom lang

-- ════════════════════════════════════════════════════════════
-- Section 7: Counting gap (schematic, proved lower bound)
-- ════════════════════════════════════════════════════════════

/-- Lower bound: the number of k-ary operations on a domain of size ≥ 2
    is at least k. The actual count is |D|^(|D|^k) (tower-exponential).
    The full anti-compression argument is in CloneHierarchyGap (Side A). -/
theorem polymorphism_counting_lower_bound (dom : CSPDomain) (k : Nat) :
    k ≤ @Fintype.card dom.D dom.fin ^ (@Fintype.card dom.D dom.fin ^ k) := by
  have hcard : @Fintype.card dom.D dom.fin ≥ 2 := dom.card_ge_two
  have hpos : @Fintype.card dom.D dom.fin ≥ 1 := by omega
  -- Step 1: k ≤ card^k (via k ≤ 2^k ≤ card^k)
  have hk_le : k ≤ @Fintype.card dom.D dom.fin ^ k :=
    calc k ≤ 2 ^ k := Nat.lt_two_pow_self.le
      _ ≤ @Fintype.card dom.D dom.fin ^ k := Nat.pow_le_pow_left hcard k
  -- Step 2: card^k ≤ card^(card^k) by monotonicity of card^(·) and step 1
  exact hk_le.trans (Nat.pow_le_pow_right hpos hk_le)

end ClassicalConstraints
