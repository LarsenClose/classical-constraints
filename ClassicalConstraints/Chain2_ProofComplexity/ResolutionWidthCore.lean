/-
  ClassicalConstraints/ResolutionWidthCore.lean
  Resolution proof system with width and size measures.

  Resolution: from clauses C ∨ x and D ∨ ¬x, derive C ∨ D.
  Width = maximum clause size in a refutation. Size = number of lines.

  Key content:
  - Literal, Clause (abbrev for Finset), CNF, ResolutionStep, ResolutionRefutation
  - Soundness of resolution
  - Width and size measures
  - Ben-Sasson-Wigderson width-size relationship (as structure)
  - ResolutionWidthLowerBound for families
  - BooleanCircuit (used by FeasibleInterpolationBridge)

  STATUS: 0 sorry. Classical.choice allowed.
-/

import ClassicalConstraints.Shared.Basic
import ClassicalConstraints.Shared.SATPresheafCore
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

namespace ClassicalConstraints

-- ════════════════════════════════════════════════════════════
-- Section 1: Literals and Clauses
-- ════════════════════════════════════════════════════════════

/-- A literal is a variable index paired with a polarity. -/
structure Literal (n : Nat) where
  /-- Which variable (index into the n variables) -/
  var : Fin n
  /-- Polarity: true = positive, false = negative -/
  pos : Bool
  deriving DecidableEq, Repr

/-- The negation of a literal. -/
def Literal.neg {n : Nat} (l : Literal n) : Literal n :=
  ⟨l.var, !l.pos⟩

/-- Negation is an involution. -/
theorem literal_neg_neg {n : Nat} (l : Literal n) :
    l.neg.neg = l := by
  simp [Literal.neg, Bool.not_not]

/-- A clause is a finite set of literals (abbrev so Finset instances apply). -/
abbrev Clause (n : Nat) := Finset (Literal n)

/-- The width of a clause: the number of literals. -/
def Clause.width {n : Nat} (c : Clause n) : Nat := c.card

/-- The empty clause (falsity). -/
def Clause.empty (n : Nat) : Clause n := ∅

-- ════════════════════════════════════════════════════════════
-- Section 2: Assignments and Satisfaction
-- ════════════════════════════════════════════════════════════

/-- An assignment maps each variable to a Boolean. -/
def CNFAssignment (n : Nat) := Fin n → Bool

/-- A literal is satisfied by an assignment. -/
def Literal.satisfied {n : Nat} (l : Literal n) (a : CNFAssignment n) : Bool :=
  if l.pos then a l.var else !a l.var

/-- A literal and its negation cannot both be satisfied. -/
theorem literal_neg_unsat {n : Nat} (l : Literal n) (a : CNFAssignment n) :
    ¬(l.satisfied a = true ∧ l.neg.satisfied a = true) := by
  cases hp : l.pos <;> cases hv : (a l.var) <;>
    simp [Literal.satisfied, Literal.neg, hp, hv]

/-- A clause is satisfied if at least one literal is satisfied. -/
def Clause.satisfied {n : Nat} (c : Clause n) (a : CNFAssignment n) : Prop :=
  ∃ l ∈ c, Literal.satisfied l a = true

/-- The empty clause is unsatisfiable. -/
theorem empty_clause_unsat {n : Nat} (a : CNFAssignment n) :
    ¬Clause.satisfied (Clause.empty n) a := by
  simp [Clause.satisfied, Clause.empty]

-- ════════════════════════════════════════════════════════════
-- Section 3: CNF Formulas
-- ════════════════════════════════════════════════════════════

/-- A CNF formula is a list of clauses over n variables. -/
structure CNF where
  /-- Number of variables -/
  num_vars : Nat
  /-- The clauses -/
  clauses : List (Clause num_vars)

/-- A CNF formula is satisfied if all clauses are satisfied. -/
def CNF.satisfied (φ : CNF) (a : CNFAssignment φ.num_vars) : Prop :=
  ∀ c ∈ φ.clauses, Clause.satisfied c a

/-- A CNF formula is unsatisfiable. -/
def CNF.unsatisfiable (φ : CNF) : Prop :=
  ∀ a : CNFAssignment φ.num_vars, ¬φ.satisfied a

-- ════════════════════════════════════════════════════════════
-- Section 4: Resolution Steps and Refutations
-- ════════════════════════════════════════════════════════════

/-- A resolution step: from two clauses containing complementary literals,
    derive the resolvent. -/
structure ResolutionStep (n : Nat) where
  /-- The first parent clause -/
  clause1 : Clause n
  /-- The second parent clause -/
  clause2 : Clause n
  /-- The pivot variable -/
  pivot : Fin n
  /-- Clause 1 contains the positive literal of the pivot -/
  h_pos : (⟨pivot, true⟩ : Literal n) ∈ clause1
  /-- Clause 2 contains the negative literal of the pivot -/
  h_neg : (⟨pivot, false⟩ : Literal n) ∈ clause2

/-- The resolvent of a resolution step: union of both clauses minus
    the pivot literals. -/
def ResolutionStep.resolvent {n : Nat} (step : ResolutionStep n) : Clause n :=
  (step.clause1.erase ⟨step.pivot, true⟩) ∪ (step.clause2.erase ⟨step.pivot, false⟩)

/-- Soundness: the resolvent is a semantic consequence of its parents.
    If both parents are satisfied, the resolvent is also satisfied. -/
theorem resolution_sound {n : Nat} (step : ResolutionStep n)
    (a : CNFAssignment n)
    (h1 : Clause.satisfied step.clause1 a)
    (h2 : Clause.satisfied step.clause2 a) :
    Clause.satisfied step.resolvent a := by
  obtain ⟨l1, hl1_mem, hl1_sat⟩ := h1
  obtain ⟨l2, hl2_mem, hl2_sat⟩ := h2
  simp only [Clause.satisfied, ResolutionStep.resolvent, Finset.mem_union, Finset.mem_erase]
  -- Case split on pivot polarity
  by_cases hpiv : a step.pivot = true
  · -- pivot is true: negative literal ⟨pivot, false⟩ is unsatisfied
    -- So l2 ≠ ⟨pivot, false⟩
    have hl2_ne : l2 ≠ ⟨step.pivot, false⟩ := by
      intro heq; subst heq
      simp [Literal.satisfied, hpiv] at hl2_sat
    -- l1 may or may not equal ⟨pivot, true⟩. Either way, use l2.
    -- If l1 ≠ ⟨pivot, true⟩, use l1 on left side.
    -- Use l2 on right side since l2 ≠ ⟨pivot, false⟩.
    exact ⟨l2, Or.inr ⟨hl2_ne, hl2_mem⟩, hl2_sat⟩
  · -- pivot is false: positive literal ⟨pivot, true⟩ is unsatisfied
    have hpiv_false : a step.pivot = false := Bool.eq_false_iff.mpr (fun h => hpiv h)
    have hl1_ne : l1 ≠ ⟨step.pivot, true⟩ := by
      intro heq; subst heq
      simp [Literal.satisfied, hpiv_false] at hl1_sat
    exact ⟨l1, Or.inl ⟨hl1_ne, hl1_mem⟩, hl1_sat⟩

/-- The resolvent has width at most width(C1) + width(C2) - 2. -/
theorem resolvent_width_bound {n : Nat} (step : ResolutionStep n) :
    step.resolvent.card ≤ step.clause1.card + step.clause2.card - 2 := by
  simp only [ResolutionStep.resolvent]
  have hc1_pos : step.clause1.card ≥ 1 := Finset.card_pos.mpr ⟨_, step.h_pos⟩
  have hc2_pos : step.clause2.card ≥ 1 := Finset.card_pos.mpr ⟨_, step.h_neg⟩
  have h1 : (step.clause1.erase ⟨step.pivot, true⟩).card ≤ step.clause1.card - 1 :=
    Nat.le_sub_one_of_lt (Finset.card_erase_lt_of_mem step.h_pos)
  have h2 : (step.clause2.erase ⟨step.pivot, false⟩).card ≤ step.clause2.card - 1 :=
    Nat.le_sub_one_of_lt (Finset.card_erase_lt_of_mem step.h_neg)
  have hunion := Finset.card_union_le (step.clause1.erase ⟨step.pivot, true⟩)
                                       (step.clause2.erase ⟨step.pivot, false⟩)
  omega

/-- A resolution refutation of a CNF formula: a sequence of derived clauses
    ending in the empty clause, where each derived clause is either an axiom
    (initial clause from the formula) or obtained by a resolution step from
    two earlier clauses. -/
structure ResolutionRefutation (φ : CNF) where
  /-- The sequence of derived clauses -/
  lines : List (Clause φ.num_vars)
  /-- The last line is the empty clause -/
  h_derives_empty : lines.getLast? = some (Clause.empty φ.num_vars)
  /-- Lines is nonempty -/
  h_nonempty : lines ≠ []
  /-- Each line is either an axiom or a resolvent of two earlier lines -/
  h_valid : ∀ (i : Fin lines.length),
    (lines[i] ∈ φ.clauses) ∨
    (∃ (j k : Fin lines.length) (step : ResolutionStep φ.num_vars),
      j.val < i.val ∧ k.val < i.val ∧
      step.clause1 = lines[j] ∧ step.clause2 = lines[k] ∧
      step.resolvent = lines[i])

/-- The width of a resolution refutation: maximum clause width. -/
def ResolutionRefutation.width {φ : CNF} (ref : ResolutionRefutation φ) : Nat :=
  ref.lines.foldl (fun acc c => max acc c.card) 0

/-- The size of a resolution refutation: number of lines. -/
def ResolutionRefutation.size {φ : CNF} (ref : ResolutionRefutation φ) : Nat :=
  ref.lines.length

-- ════════════════════════════════════════════════════════════
-- Section 5: Width-Size Relationship
-- ════════════════════════════════════════════════════════════

/-- The Ben-Sasson-Wigderson width-size relationship (stated as structure).
    If a CNF formula with initial clause width k requires resolution width w,
    then any resolution refutation has size at least w - k + 1.
    This captures the monotone growth without the full exponential accounting. -/
structure WidthSizeRelation (φ : CNF) where
  /-- Initial clause width bound -/
  initial_width : Nat
  /-- Every initial clause has width at most initial_width -/
  h_initial : ∀ c ∈ φ.clauses, c.card ≤ initial_width
  /-- Width-to-size lower bound -/
  h_width_implies_size : ∀ (ref : ResolutionRefutation φ),
    ref.size ≥ ref.width - initial_width + 1

-- ════════════════════════════════════════════════════════════
-- Section 6: Width Lower Bounds for Families
-- ════════════════════════════════════════════════════════════

/-- The minimum width of any refutation of φ (as a Prop). -/
def minResolutionWidth (φ : CNF) (_h_unsat : φ.unsatisfiable) : Nat → Prop :=
  fun w => (∃ ref : ResolutionRefutation φ, ref.width ≤ w) ∧
           (∀ ref : ResolutionRefutation φ, ref.width ≥ w)

/-- A width lower bound for a specific family: a family of unsatisfiable
    CNFs indexed by size, with growing width requirement. -/
structure ResolutionWidthLowerBound where
  /-- The CNF family -/
  family : Nat → CNF
  /-- Each member is unsatisfiable -/
  h_unsat : ∀ n, (family n).unsatisfiable
  /-- Width grows: resolution width of family n is at least w(n) -/
  width_bound : Nat → Nat
  /-- The width bound grows without bound -/
  h_width_grows : ∀ K, ∃ n, width_bound n > K
  /-- Every refutation of family n has width at least width_bound n -/
  h_width_lower : ∀ n (ref : ResolutionRefutation (family n)),
    ref.width ≥ width_bound n

/-- Width lower bounds imply size lower bounds via the width-size relation.
    If every refutation has width ≥ w(n) and initial width is k,
    then size ≥ w(n) - k + 1. -/
theorem width_lower_implies_size_lower
    (lb : ResolutionWidthLowerBound) (wsr : ∀ n, WidthSizeRelation (lb.family n))
    (n : Nat) (ref : ResolutionRefutation (lb.family n)) :
    ref.size ≥ lb.width_bound n - (wsr n).initial_width + 1 := by
  have hwidth := lb.h_width_lower n ref
  have hsize := (wsr n).h_width_implies_size ref
  omega

-- ════════════════════════════════════════════════════════════
-- Section 7: BooleanCircuit (used by FeasibleInterpolationBridge)
-- ════════════════════════════════════════════════════════════

/-- A Boolean circuit over n input variables.
    Abstracted to its functional behavior and complexity measures. -/
structure BooleanCircuit (n : Nat) where
  /-- Evaluate the circuit on an input assignment. -/
  eval : (Fin n → Bool) → Bool
  /-- Circuit depth (longest input-to-output path). -/
  depth : Nat
  /-- Total number of gates. -/
  gateCount : Nat

/-- A Boolean circuit computing a constant function has depth 0. -/
def BooleanCircuit.const (n : Nat) (v : Bool) : BooleanCircuit n where
  eval := fun _ => v
  depth := 0
  gateCount := 0

end ClassicalConstraints
