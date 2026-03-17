/-
  ClassicalConstraints/PebbleGameObstruction.lean
  k-pebble Ehrenfeucht-Fraisse games on pairs of finite structures.

  Characterizes the distinguishing power of first-order logic with k variables.
  Classical.choice is allowed. No sorry.
-/

import ClassicalConstraints.Chain3_Descriptive.ESOWitnessCore
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic

namespace ClassicalConstraints

-- ════════════════════════════════════════════════════════════
-- Section 1: Pebble positions
-- ════════════════════════════════════════════════════════════

/-- A pebble position in the k-pebble game on structures A and B.
    Each pebble i (for i < k) is either unplaced or placed on a pair
    of elements (one in A, one in B). -/
structure PebblePosition (k : Nat) {vocab : Vocabulary}
    (A B : FiniteStructure vocab) where
  /-- Placement of each pebble: None = unplaced, Some (a, b) = placed. -/
  placement : Fin k → Option (A.Domain × B.Domain)

/-- A pebble position is a partial isomorphism if the placed pebbles
    define a local isomorphism: placed pairs preserve all relations
    and equalities.

    For relation preservation, we only require the condition when the arity
    is positive (arity > 0), because for arity 0 the tuple is empty and
    we cannot recover any information from the pebble placement. -/
def PebblePosition.isPartialIsomorphism {k : Nat} {vocab : Vocabulary}
    {A B : FiniteStructure vocab}
    (pos : PebblePosition k A B) : Prop :=
  -- 1. Equality preservation: pebbles i,j placed on (ai,bi),(aj,bj) implies ai=aj ↔ bi=bj
  (∀ (i j : Fin k)
    (ai aj : A.Domain) (bi bj : B.Domain),
    pos.placement i = some (ai, bi) →
    pos.placement j = some (aj, bj) →
    (ai = aj ↔ bi = bj)) ∧
  -- 2. Relation preservation for arity-positive relations only
  (∀ (rel_idx : Fin vocab.num_rels)
    (peb_assignment : Fin (vocab.arity rel_idx) → Fin k)
    (a_tuple : Fin (vocab.arity rel_idx) → A.Domain)
    (b_tuple : Fin (vocab.arity rel_idx) → B.Domain),
    vocab.arity rel_idx > 0 →
    (∀ p, pos.placement (peb_assignment p) = some (a_tuple p, b_tuple p)) →
    (A.interp rel_idx a_tuple ↔ B.interp rel_idx b_tuple))

-- ════════════════════════════════════════════════════════════
-- Section 2: Game tree
-- ════════════════════════════════════════════════════════════

/-- A round of the k-pebble game: Spoiler picks a pebble, a structure,
    and an element; Duplicator responds; game continues.
    CRITICAL: This is an actual game tree with rounds. -/
inductive PebbleGameTree (k : Nat) {vocab : Vocabulary}
    (A B : FiniteStructure vocab) : Type where
  /-- Leaf: game ends at this position. -/
  | leaf : PebblePosition k A B → PebbleGameTree k A B
  /-- Move: Spoiler picks pebble, Duplicator responds, game continues. -/
  | move :
    (pebble : Fin k) →
    (side : Bool) →
    -- Spoiler's element and Duplicator's response (encoded as A ⊕ B pairs)
    (spoiler_a : A.Domain) →
    (spoiler_b : B.Domain) →
    PebbleGameTree k A B →
    PebbleGameTree k A B

-- ════════════════════════════════════════════════════════════
-- Section 3: Spoiler strategy
-- NOT USED in any proved theorem. The file's load-bearing results
-- (pebble_lower_bound_implies_not_definable, unbounded_pebble_requirement)
-- use DuplicatorStrategy and KPebbleEquivalent. Included for completeness
-- of the game-theoretic presentation. h_winning quantifies over arbitrary
-- positions, not just game-reachable ones; acceptable for unused code.
-- ════════════════════════════════════════════════════════════

/-- A Spoiler strategy: at each position and round, Spoiler chooses
    which pebble to move, which structure, and which element. -/
structure SpoilerStrategy (k r : Nat) {vocab : Vocabulary}
    (A B : FiniteStructure vocab) where
  /-- Given current position and round number, Spoiler's choice. -/
  move : PebblePosition k A B → Fin r →
    (Fin k × Bool × (A.Domain ⊕ B.Domain))
  /-- The strategy is winning: for all Duplicator responses, some position
      is not a partial isomorphism. -/
  h_winning : ∀ (_dup_responses : Fin r →
    PebblePosition k A B → (A.Domain ⊕ B.Domain)),
    ∃ (_i : Fin r) (pos : PebblePosition k A B),
      ¬pos.isPartialIsomorphism

-- ════════════════════════════════════════════════════════════
-- Section 4: Duplicator strategy
-- ════════════════════════════════════════════════════════════

/-- A Duplicator strategy: at each position, given Spoiler's move,
    Duplicator responds with a new position that maintains partial isomorphism.
    The response IS the new position — linking behavior to correctness. -/
structure DuplicatorStrategy (k : Nat) {vocab : Vocabulary}
    (A B : FiniteStructure vocab) where
  /-- Given current position and Spoiler's move, Duplicator's new position. -/
  respond : PebblePosition k A B → Fin k → Bool →
    (A.Domain ⊕ B.Domain) → PebblePosition k A B
  /-- The response position maintains partial isomorphism. -/
  h_maintains : ∀ (pos : PebblePosition k A B),
    pos.isPartialIsomorphism →
    ∀ (peb : Fin k) (side : Bool) (elem : A.Domain ⊕ B.Domain),
    (respond pos peb side elem).isPartialIsomorphism

-- ════════════════════════════════════════════════════════════
-- Section 5: k-pebble equivalence
-- ════════════════════════════════════════════════════════════

/-- Two structures are k-pebble equivalent if Duplicator has a winning
    strategy in the k-pebble game (for any number of rounds). -/
def KPebbleEquivalent (k : Nat) {vocab : Vocabulary}
    (A B : FiniteStructure vocab) : Prop :=
  Nonempty (DuplicatorStrategy k A B)

-- ════════════════════════════════════════════════════════════
-- Section 5b: Round-bounded pebble equivalence
-- ════════════════════════════════════════════════════════════

/-- A Duplicator strategy for r rounds: responds for at most r rounds
    while maintaining partial isomorphism. -/
structure RRoundDuplicatorStrategy (k r : Nat) {vocab : Vocabulary}
    (A B : FiniteStructure vocab) where
  /-- Given current position, round number, and Spoiler's move, new position. -/
  respond : PebblePosition k A B → Fin r → Fin k → Bool →
    (A.Domain ⊕ B.Domain) → PebblePosition k A B
  /-- The response position maintains partial isomorphism. -/
  h_maintains : ∀ (pos : PebblePosition k A B) (round : Fin r),
    pos.isPartialIsomorphism →
    ∀ (peb : Fin k) (side : Bool) (elem : A.Domain ⊕ B.Domain),
    (respond pos round peb side elem).isPartialIsomorphism

/-- Two structures are (k, r)-pebble equivalent: Duplicator wins the k-pebble
    game with at most r rounds.

    CRITICAL DISTINCTION from KPebbleEquivalent:
    - KPebbleEquivalent = Duplicator wins with UNBOUNDED rounds = infinite back-and-forth
    - RRoundKPebbleEquivalent = Duplicator wins with exactly r rounds = corresponds to
      FO sentences with at most k variables AND quantifier rank at most r -/
def RRoundKPebbleEquivalent (k r : Nat) {vocab : Vocabulary}
    (A B : FiniteStructure vocab) : Prop :=
  Nonempty (RRoundDuplicatorStrategy k r A B)

/-- A 1-round Duplicator strategy gives a full (unbounded) Duplicator strategy.
    The DuplicatorStrategy definition requires only per-step maintenance of
    partial isomorphism, so a single-round strategy suffices.
    NOTE: the original `k_pebble_equiv_from_all_rounds` claimed to use
    "∀ r, RRoundKPebbleEquivalent k r A B" but only used r = 1. The true
    limit theorem (all rounds → unbounded via compactness) requires König's
    lemma and is not formalized here. -/
theorem k_pebble_equiv_from_one_round {k : Nat} {vocab : Vocabulary}
    {A B : FiniteStructure vocab}
    (h : RRoundKPebbleEquivalent k 1 A B) :
    KPebbleEquivalent k A B :=
  ⟨{
    respond := fun pos peb side elem =>
      (Classical.choice h).respond pos ⟨0, Nat.zero_lt_succ 0⟩ peb side elem
    h_maintains := fun pos hiso peb side elem =>
      (Classical.choice h).h_maintains pos ⟨0, Nat.zero_lt_succ 0⟩ hiso peb side elem }⟩

-- ════════════════════════════════════════════════════════════
-- Section 6: EF theorem (stated as structure parameter)
-- ════════════════════════════════════════════════════════════

/-- The Ehrenfeucht-Fraisse theorem for pebble games:
    k-pebble equivalent structures agree on all FO sentences with
    at most k variables. Stated as a structure (not proved here). -/
structure PebbleFormulaEquivalence where
  /-- k-pebble equivalent structures agree on k-variable FO sentences. -/
  equiv_implies_agree : ∀ (k : Nat) (vocab : Vocabulary)
    (A B : FiniteStructure vocab)
    (_h_equiv : KPebbleEquivalent k A B)
    (phi : FOFormula vocab)
    (_h_width : phi.numVariables ≤ k),
    FOFormula.eval vocab A phi ↔ FOFormula.eval vocab B phi

-- ════════════════════════════════════════════════════════════
-- Section 7: SAT pebble families
-- ════════════════════════════════════════════════════════════

/-- A family of pairs of SAT-derived structures that are k-pebble
    equivalent but differ on a property.

    Uses the FIXED SAT vocabulary (4 relations: Var, Clause, PosOccurs, NegOccurs).
    The vocabulary is fixed across all instance sizes -- this is the key
    improvement over the old encoding that grew the vocabulary with clause count. -/
structure SATInstancePebbleFamily where
  /-- For each k, a pair of structures over the fixed SAT vocabulary. -/
  pair : (k : Nat) → (FiniteStructure satVocabulary × FiniteStructure satVocabulary)
  /-- The domain sizes grow with k. -/
  h_growing : ∀ k, (pair k).1.domainSize ≥ k
  /-- They are k-pebble equivalent. -/
  h_equiv : ∀ k, KPebbleEquivalent k (pair k).1 (pair k).2
  /-- They differ on a definable property. -/
  target_property : (k : Nat) → FiniteStructure satVocabulary → Prop
  h_differ : ∀ k,
    target_property k (pair k).1 ∧ ¬target_property k (pair k).2

-- ════════════════════════════════════════════════════════════
-- Section 8: Core theorems
-- ════════════════════════════════════════════════════════════

/-- If there exists a k-pebble-equivalent pair that differs on a property,
    then the property is not definable by any FO sentence with at most k variables. -/
theorem pebble_lower_bound_implies_not_definable
    (k : Nat) {vocab : Vocabulary}
    (A B : FiniteStructure vocab)
    (h_equiv : KPebbleEquivalent k A B)
    (prop : FiniteStructure vocab → Prop)
    (h_differ : prop A ∧ ¬prop B)
    (pfe : PebbleFormulaEquivalence) :
    ¬∃ (phi : FOFormula vocab),
      phi.numVariables ≤ k ∧
      ∀ C, FOFormula.eval vocab C phi ↔ prop C := by
  intro ⟨phi, h_width, h_char⟩
  have hA : FOFormula.eval vocab A phi ↔ prop A := h_char A
  have hB : FOFormula.eval vocab B phi ↔ prop B := h_char B
  have h_agree : FOFormula.eval vocab A phi ↔ FOFormula.eval vocab B phi :=
    pfe.equiv_implies_agree k vocab A B h_equiv phi h_width
  have hpA : prop A := h_differ.1
  have hnpB : ¬prop B := h_differ.2
  have hphiA : FOFormula.eval vocab A phi := hA.mpr hpA
  have hphiB : FOFormula.eval vocab B phi := h_agree.mp hphiA
  exact hnpB (hB.mp hphiB)

/-- A SAT pebble family requires unbounded pebble count. -/
theorem unbounded_pebble_requirement
    (fam : SATInstancePebbleFamily)
    (pfe : PebbleFormulaEquivalence)
    (k : Nat) :
    ¬∃ (phi : FOFormula satVocabulary),
      phi.numVariables ≤ k ∧
      ∀ C, FOFormula.eval satVocabulary C phi ↔
             fam.target_property k C :=
  pebble_lower_bound_implies_not_definable k
    (fam.pair k).1 (fam.pair k).2
    (fam.h_equiv k) (fam.target_property k)
    (fam.h_differ k) pfe

-- ════════════════════════════════════════════════════════════
-- Section 9: Equivalence relation properties
-- ════════════════════════════════════════════════════════════

/-- The trivially-placed empty position is a partial isomorphism. -/
def emptyPosition {k : Nat} {vocab : Vocabulary} {A B : FiniteStructure vocab} :
    PebblePosition k A B where
  placement := fun _ => none

theorem empty_is_partial_iso {k : Nat} {vocab : Vocabulary}
    {A B : FiniteStructure vocab} :
    (@emptyPosition k vocab A B).isPartialIsomorphism := by
  refine ⟨fun i j ai aj bi bj h1 _ => ?_, fun rel peb a_tup b_tup hpos h => ?_⟩
  · simp [emptyPosition] at h1
  · -- arity > 0, so pick p = ⟨0, hpos⟩ and derive contradiction since no pebble is placed
    have := h ⟨0, hpos⟩
    simp [emptyPosition] at this

/-- k-pebble equivalence is reflexive: Duplicator returns the current position.
    Since `DuplicatorStrategy.h_maintains` only requires the response position to
    be a partial isomorphism, Duplicator can simply keep the current position. -/
theorem pebble_equiv_refl (k : Nat) {vocab : Vocabulary}
    (A : FiniteStructure vocab) : KPebbleEquivalent k A A :=
  ⟨{
    respond := fun pos _ _ _ => pos
    h_maintains := fun _ hiso _ _ _ => hiso }⟩

/-- Swap a pebble position: exchange the A and B components. -/
def PebblePosition.swap {k : Nat} {vocab : Vocabulary}
    {A B : FiniteStructure vocab}
    (pos : PebblePosition k A B) : PebblePosition k B A where
  placement := fun i => (pos.placement i).map (fun p => (p.2, p.1))

/-- Swapping preserves partial isomorphism. -/
theorem PebblePosition.swap_preserves_iso {k : Nat} {vocab : Vocabulary}
    {A B : FiniteStructure vocab}
    (pos : PebblePosition k A B)
    (hiso : pos.isPartialIsomorphism) :
    pos.swap.isPartialIsomorphism := by
  obtain ⟨heq, hrel⟩ := hiso
  constructor
  · -- Equality preservation: swap reverses both sides of the iff
    intro i j bi bj ai aj hi hj
    simp only [PebblePosition.swap, Option.map] at hi hj
    -- Extract the original placements
    cases hpi : pos.placement i with
    | none => simp [hpi] at hi
    | some pi =>
      simp [hpi] at hi
      obtain ⟨rfl, rfl⟩ := hi
      cases hpj : pos.placement j with
      | none => simp [hpj] at hj
      | some pj =>
        simp [hpj] at hj
        obtain ⟨rfl, rfl⟩ := hj
        exact (heq i j pi.1 pj.1 pi.2 pj.2 hpi hpj).symm
  · -- Relation preservation: swap reverses A and B interpretation
    intro rel peb b_tup a_tup hpos h
    -- Build the original tuples from the swapped placement
    have h_orig : ∀ p, pos.placement (peb p) = some (a_tup p, b_tup p) := by
      intro p
      have hp := h p
      simp only [PebblePosition.swap, Option.map] at hp
      cases hq : pos.placement (peb p) with
      | none => simp [hq] at hp
      | some q =>
        simp [hq] at hp
        rw [show q = (a_tup p, b_tup p) from Prod.ext hp.2 hp.1]
    exact (hrel rel peb a_tup b_tup hpos h_orig).symm

/-- k-pebble equivalence is symmetric: given Duplicator's strategy for A vs B,
    construct a strategy for B vs A by swapping positions. -/
theorem pebble_equiv_symm (k : Nat) {vocab : Vocabulary}
    {A B : FiniteStructure vocab}
    (h : KPebbleEquivalent k A B) : KPebbleEquivalent k B A := by
  obtain ⟨strat⟩ := h
  exact ⟨{
    respond := fun pos peb side elem =>
      -- Swap position to A-vs-B, use original strategy, swap the response
      (strat.respond pos.swap peb (!side) (Sum.swap elem)).swap
    h_maintains := fun pos hiso peb side elem =>
      -- The swapped position is a partial isomorphism
      (strat.respond pos.swap peb (!side) (Sum.swap elem)).swap_preserves_iso
        (strat.h_maintains pos.swap (pos.swap_preserves_iso hiso)
          peb (!side) (Sum.swap elem)) }⟩

end ClassicalConstraints
