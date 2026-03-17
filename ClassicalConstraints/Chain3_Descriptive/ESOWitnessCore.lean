/-
  ClassicalConstraints/ESOWitnessCore.lean
  NP via existential second-order logic (ESO) and SAT satisfiability.

  Builds the descriptive complexity infrastructure from scratch:
  finite relational structures, first-order formulas with quantifier
  depth tracking, ESO formulas, and SAT-as-structure encoding.

  FIXED VOCABULARY: SAT instances are encoded using a FIXED relational
  vocabulary with 4 relations (Var, Clause, PosOccurs, NegOccurs).
  The domain contains both variables and clauses. This is the standard
  clause-variable incidence encoding, giving a fixed signature across
  all instance sizes — not a vocabulary that grows with the number of clauses.

  Classical.choice is allowed. No sorry.
-/

import ClassicalConstraints.Shared.Basic
import ClassicalConstraints.Shared.SATPresheafCore
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic

namespace ClassicalConstraints

-- ════════════════════════════════════════════════════════════
-- Section 1: Relational vocabulary
-- ════════════════════════════════════════════════════════════

/-- A relational vocabulary: a list of relation symbols with their arities.
    No function symbols (finite model theory convention). -/
structure Vocabulary where
  num_rels : Nat
  arity : Fin num_rels → Nat

def Vocabulary.empty : Vocabulary where
  num_rels := 0
  arity := fun i => i.elim0

-- ════════════════════════════════════════════════════════════
-- Section 2: Fixed SAT vocabulary (clause-variable incidence)
-- ════════════════════════════════════════════════════════════

/-- The FIXED SAT vocabulary: 4 relation symbols, independent of instance size.

    Clause-variable incidence encoding:
    - Index 0: Var (unary) — marks variable-type domain elements
    - Index 1: Clause (unary) — marks clause-type domain elements
    - Index 2: PosOccurs (binary) — variable appears positively in clause
    - Index 3: NegOccurs (binary) — variable appears negatively in clause

    The domain contains both variables and clauses, so the vocabulary
    never changes with instance size. This is essential for descriptive
    complexity: a vocabulary that changes with instance size breaks the
    FO / pebble / locality story. -/
def satVocabulary : Vocabulary where
  num_rels := 4
  arity i := match i.val with
    | 0 => 1  -- Var: unary
    | 1 => 1  -- Clause: unary
    | 2 => 2  -- PosOccurs: binary
    | _ => 2  -- NegOccurs: binary

theorem satVocab_num_rels : satVocabulary.num_rels = 4 := rfl

theorem satVocab_arity_pos (i : Fin satVocabulary.num_rels) :
    0 < satVocabulary.arity i := by
  have hi := i.isLt
  simp only [satVocabulary] at hi ⊢
  match i.val, hi with
  | 0, _ => decide
  | 1, _ => decide
  | 2, _ => decide
  | 3, _ => decide

theorem satVocab_arity_23 (i : Fin satVocabulary.num_rels) (hi : 2 ≤ i.val) :
    1 < satVocabulary.arity i := by
  have hlt := i.isLt
  simp only [satVocabulary] at hlt ⊢
  match i.val, hi, hlt with
  | 2, _, _ => decide
  | 3, _, _ => decide

-- ════════════════════════════════════════════════════════════
-- Section 3: Finite relational structures
-- ════════════════════════════════════════════════════════════

/-- A finite relational structure over a vocabulary.
    CRITICAL: the domain has an explicit Fintype instance. -/
structure FiniteStructure (vocab : Vocabulary) where
  Domain : Type
  h_fintype : Fintype Domain
  h_nonempty : Nonempty Domain
  h_deceq : DecidableEq Domain
  interp : (i : Fin vocab.num_rels) → (Fin (vocab.arity i) → Domain) → Prop
  h_interp_dec : ∀ i t, Decidable (interp i t)

def FiniteStructure.domainSize {vocab : Vocabulary}
    (A : FiniteStructure vocab) : Nat :=
  @Fintype.card A.Domain A.h_fintype

-- ════════════════════════════════════════════════════════════
-- Section 4: Ordered finite structures
-- ════════════════════════════════════════════════════════════

/-- A finite structure equipped with a total order on its domain.
    CRITICAL for Immerman-Vardi: P = FO+LFP holds ONLY on ordered structures. -/
structure OrderedFiniteStructure (vocab : Vocabulary)
    extends FiniteStructure vocab where
  order : Domain → Domain → Prop
  h_order_dec : ∀ a b, Decidable (order a b)
  h_total : ∀ a b, order a b ∨ order b a
  h_trans : ∀ a b c, order a b → order b c → order a c
  h_antisymm : ∀ a b, order a b → order b a → a = b

-- ════════════════════════════════════════════════════════════
-- Section 5: First-order formulas with quantifier depth
-- ════════════════════════════════════════════════════════════

inductive FOFormula (vocab : Vocabulary) : Type where
  | feq : Nat → Nat → FOFormula vocab
  | frel : (i : Fin vocab.num_rels) → (Fin (vocab.arity i) → Nat) → FOFormula vocab
  | fneg : FOFormula vocab → FOFormula vocab
  | fconj : FOFormula vocab → FOFormula vocab → FOFormula vocab
  | fdisj : FOFormula vocab → FOFormula vocab → FOFormula vocab
  | fex : FOFormula vocab → FOFormula vocab
  | fall : FOFormula vocab → FOFormula vocab

def FOFormula.quantifierDepth {vocab : Vocabulary} : FOFormula vocab → Nat
  | .feq _ _ => 0
  | .frel _ _ => 0
  | .fneg phi => phi.quantifierDepth
  | .fconj phi psi => max phi.quantifierDepth psi.quantifierDepth
  | .fdisj phi psi => max phi.quantifierDepth psi.quantifierDepth
  | .fex phi => phi.quantifierDepth + 1
  | .fall phi => phi.quantifierDepth + 1

def FOFormula.numVariables {vocab : Vocabulary} : FOFormula vocab → Nat
  | .feq i j => max i j + 1
  | .frel _ args =>
      let indices := List.ofFn (fun k => args k)
      indices.foldl max 0 + 1
  | .fneg phi => phi.numVariables
  | .fconj phi psi => max phi.numVariables psi.numVariables
  | .fdisj phi psi => max phi.numVariables psi.numVariables
  | .fex phi => phi.numVariables
  | .fall phi => phi.numVariables

-- ════════════════════════════════════════════════════════════
-- Section 6: FO formula evaluation
-- ════════════════════════════════════════════════════════════

def FOFormula.evalWithVal {vocab : Vocabulary}
    (A : FiniteStructure vocab)
    (val : Nat → A.Domain) :
    FOFormula vocab → Prop
  | .feq i j => val i = val j
  | .frel i args => A.interp i (fun k => val (args k))
  | .fneg phi => ¬FOFormula.evalWithVal A val phi
  | .fconj phi psi =>
      FOFormula.evalWithVal A val phi ∧ FOFormula.evalWithVal A val psi
  | .fdisj phi psi =>
      FOFormula.evalWithVal A val phi ∨ FOFormula.evalWithVal A val psi
  | .fex phi =>
      ∃ a : A.Domain,
        FOFormula.evalWithVal A (fun i => if i = 0 then a else val (i - 1)) phi
  | .fall phi =>
      ∀ a : A.Domain,
        FOFormula.evalWithVal A (fun i => if i = 0 then a else val (i - 1)) phi

noncomputable def FOFormula.eval {vocab : Vocabulary}
    (_ : Vocabulary) (A : FiniteStructure vocab) (phi : FOFormula vocab) : Prop :=
  FOFormula.evalWithVal A (fun _ => Classical.choice A.h_nonempty) phi

-- ════════════════════════════════════════════════════════════
-- Section 7: Vocabulary expansion (for ESO)
-- ════════════════════════════════════════════════════════════

def expandVocabByOne (vocab : Vocabulary) (extra_arity : Nat) : Vocabulary where
  num_rels := vocab.num_rels + 1
  arity i :=
    if h : i.val < vocab.num_rels then vocab.arity ⟨i.val, h⟩
    else extra_arity

-- ════════════════════════════════════════════════════════════
-- Section 8: ESO formulas
-- ════════════════════════════════════════════════════════════

/-- An existential second-order formula: ∃R1...Rk. phi(R1,...,Rk)
    where the existential quantification ranges over ALL relations
    of the given arities on the domain — this is what makes ESO = NP.

    The expanded vocabulary data is EXPLICIT: the first `vocab.num_rels`
    relation symbols in `expanded_vocab` correspond to the original relations
    (preserving arities), and the next `num_rel_vars` are the existentially
    quantified relation variables. -/
structure ESOFormula (vocab : Vocabulary) where
  num_rel_vars : Nat
  rel_var_arity : Fin num_rel_vars → Nat
  expanded_vocab : Vocabulary
  h_expansion : expanded_vocab.num_rels = vocab.num_rels + num_rel_vars
  /-- Original relation arities are preserved in the expanded vocab. -/
  h_orig_embed : ∀ (i : Fin vocab.num_rels),
    expanded_vocab.arity ⟨i.val,
      h_expansion ▸ (Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right _ _))⟩ = vocab.arity i
  body : FOFormula expanded_vocab

noncomputable def ESOFormula.satisfied {vocab : Vocabulary}
    (phi : ESOFormula vocab) (A : FiniteStructure vocab) : Prop :=
  ∃ (expanded : FiniteStructure phi.expanded_vocab),
    ∃ (_h_dom : expanded.Domain = A.Domain),
    FOFormula.evalWithVal expanded
      (fun _ => Classical.choice expanded.h_nonempty)
      phi.body

-- ════════════════════════════════════════════════════════════
-- Section 9: SAT as finite structure (FIXED VOCABULARY)
-- ════════════════════════════════════════════════════════════

/-- Convert a SAT instance to a finite relational structure using the
    FIXED clause-variable incidence vocabulary.

    Domain = Fin(num_vars + num_clauses + 1) where:
    - Elements 0..num_vars-1: variable elements (Var holds)
    - Elements num_vars..num_vars+num_clauses-1: clause elements (Clause holds)
    - Element num_vars+num_clauses: dummy (ensures nonempty when both counts are 0)

    Relations:
    - Var(i): i < num_vars
    - Clause(i): num_vars ≤ i < num_vars + num_clauses
    - PosOccurs(v, c): variable v appears positively in clause (c - num_vars)
    - NegOccurs(v, c): variable v appears negatively in clause (c - num_vars) -/
-- satInterp: the interpretation function for satVocabulary, case-split on the 4 relations.
-- We explicitly handle each of the 4 cases (0=Var, 1=Clause, 2=PosOccurs, 3=NegOccurs).
private noncomputable def satInterp (phi : SATInstance)
    (idx : Fin satVocabulary.num_rels)
    (args : Fin (satVocabulary.arity idx) → Fin (phi.num_vars + phi.clauses.length + 1)) : Prop :=
  -- Case 0: Var (unary, arity 1)
  if h0 : idx.val = 0 then
    let v := (args ⟨0, by simp [satVocabulary, h0]⟩).val
    v < phi.num_vars
  -- Case 1: Clause (unary, arity 1)
  else if h1 : idx.val = 1 then
    let v := (args ⟨0, by simp [satVocabulary, h1]⟩).val
    phi.num_vars ≤ v ∧ v < phi.num_vars + phi.clauses.length
  -- Case 2: PosOccurs (binary, arity 2)
  else if h2 : idx.val = 2 then
    let v := (args ⟨0, by simp [satVocabulary, h2]⟩).val
    let c := (args ⟨1, by simp [satVocabulary, h2]⟩).val
    v < phi.num_vars ∧
    phi.num_vars ≤ c ∧ c < phi.num_vars + phi.clauses.length ∧
    (∃ lit ∈ (phi.clauses.getD (c - phi.num_vars) []), lit = ((v + 1 : Nat) : Int))
  -- Case 3: NegOccurs (binary, arity 2)
  else
    -- idx.val ∈ {0,1,2,3} and not 0,1,2, so idx.val = 3
    have h3 : idx.val = 3 := by
      have hlt := idx.isLt
      have h4 : satVocabulary.num_rels = 4 := rfl
      -- omega needs to know idx.val < 4, but num_rels appears as opaque in hlt.
      -- Replace: note hlt : idx.val < satVocabulary.num_rels and h4 : satVocabulary.num_rels = 4
      -- Substituting: idx.val < 4.
      -- omega can use h0, h1, h2 and hlt with h4 substituted.
      -- Use Nat.lt_of_lt_of_eq to convert.
      have hlt4 : idx.val < 4 := h4 ▸ hlt
      omega
    let v := (args ⟨0, by simp [satVocabulary, h3]⟩).val
    let c := (args ⟨1, by simp [satVocabulary, h3]⟩).val
    v < phi.num_vars ∧
    phi.num_vars ≤ c ∧ c < phi.num_vars + phi.clauses.length ∧
    (∃ lit ∈ (phi.clauses.getD (c - phi.num_vars) []), lit = -((v + 1 : Nat) : Int))

noncomputable def SATInstance.toFixedStructure (phi : SATInstance) :
    FiniteStructure satVocabulary where
  Domain := Fin (phi.num_vars + phi.clauses.length + 1)
  h_fintype := inferInstance
  h_nonempty := ⟨⟨0, by omega⟩⟩
  h_deceq := inferInstance
  interp := satInterp phi
  h_interp_dec := fun _ _ => Classical.propDecidable _

-- ════════════════════════════════════════════════════════════
-- Section 10: ESO characterization of SAT
-- ════════════════════════════════════════════════════════════

/-- SAT satisfiability is ESO-definable over the fixed SAT vocabulary.
    The ESO formula quantifies over a unary relation selecting which
    variable elements are assigned TRUE. -/
structure SATSatisfiabilityIsESO where
  phi : ESOFormula satVocabulary
  h_unary_witness : phi.num_rel_vars = 1
  h_correct : ∀ (inst : SATInstance),
    inst.Satisfiable ↔ phi.satisfied inst.toFixedStructure

-- ════════════════════════════════════════════════════════════
-- Section 11: Key theorems
-- ════════════════════════════════════════════════════════════

/-- The fixed SAT vocabulary has 4 relation symbols (sanity check). -/
theorem sat_vocab_is_fixed : satVocabulary.num_rels = 4 := rfl

/-- The SAT structure domain size. -/
theorem sat_structure_domain_size (phi : SATInstance) :
    phi.toFixedStructure.domainSize = phi.num_vars + phi.clauses.length + 1 := by
  simp [SATInstance.toFixedStructure, FiniteStructure.domainSize]

end ClassicalConstraints
