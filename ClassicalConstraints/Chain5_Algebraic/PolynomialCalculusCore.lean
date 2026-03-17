/-
  ClassicalConstraints/PolynomialCalculusCore.lean
  Polynomial Calculus (PC) proof system over a field F.

  PC derives polynomial identities from:
  - Boolean axioms: x_i^2 - x_i = 0 for each variable
  - Clause axioms: the polynomial encoding of each clause

  Rules: addition and multiplication by a variable.
  Complexity measure: DEGREE (max total degree of any polynomial in the derivation).
  This is a DYNAMIC system -- a sequence of derivation steps, not a single identity.

  STATUS: 0 sorry. Classical.choice allowed (Side B).
-/

import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Finset.Basic
import ClassicalConstraints.Shared.Basic

namespace ClassicalConstraints

open MvPolynomial

-- ================================================================
-- Section 1: SAT to polynomial encoding
-- ================================================================

/-- Encode a Boolean literal as a polynomial over F[x_1,...,x_n].
    Positive literal k > 0: maps to x_{k-1}
    Negative literal k < 0: maps to 1 - x_{|k|-1}
    Out-of-range or zero literals map to 0. -/
noncomputable def literalPoly (F : Type*) [Field F] (n : Nat) (lit : Int) :
    MvPolynomial (Fin n) F :=
  if _h₁ : lit > 0 then
    if h₂ : lit.toNat - 1 < n then
      MvPolynomial.X (⟨lit.toNat - 1, h₂⟩ : Fin n)
    else 0
  else if _h₃ : lit < 0 then
    if h₄ : (-lit).toNat - 1 < n then
      (1 : MvPolynomial (Fin n) F) - MvPolynomial.X (⟨(-lit).toNat - 1, h₄⟩ : Fin n)
    else 0
  else 0

/-- Encode a clause (disjunction of literals) as a polynomial.
    clausePoly = 0 means clause is satisfied.
    Encoding: product of (1 - literalPoly ℓ) over all literals ℓ.
    When all literals are false (clause unsatisfied), each factor is 1, product is 1. -/
noncomputable def clausePoly (F : Type*) [Field F] (n : Nat)
    (clause : List Int) : MvPolynomial (Fin n) F :=
  clause.foldl (fun (acc : MvPolynomial (Fin n) F) (lit : Int) =>
    acc * ((1 : MvPolynomial (Fin n) F) - literalPoly F n lit)) 1

-- ================================================================
-- Section 2: PC axioms
-- ================================================================

/-- The Boolean axiom for variable i: x_i^2 - x_i. -/
noncomputable def booleanAxiom (F : Type*) [Field F] (n : Nat)
    (i : Fin n) : MvPolynomial (Fin n) F :=
  MvPolynomial.X (R := F) i ^ 2 - MvPolynomial.X (R := F) i

/-- A PC axiom set for an unsatisfiable CNF formula. -/
structure PCAXioms (F : Type*) [Field F] (n : Nat) where
  /-- The clauses of the CNF formula. -/
  clauses : List (List Int)
  /-- The clause polynomials. -/
  clause_polys : List (MvPolynomial (Fin n) F)
  /-- Clause polynomials are correctly computed. -/
  h_clause_correct : clause_polys = clauses.map (clausePoly F n)

-- ================================================================
-- Section 3: PC derivation steps
-- ================================================================

/-- A single step in a PC derivation. -/
inductive PCStep (F : Type*) [Field F] (n : Nat) where
  /-- Introduce a Boolean axiom. -/
  | boolAxiom (i : Fin n) : PCStep F n
  /-- Introduce a clause axiom (by index). -/
  | clauseAxiom (idx : Nat) : PCStep F n
  /-- Add two previously derived polynomials. -/
  | add (left right : Nat) : PCStep F n
  /-- Multiply a previously derived polynomial by a variable. -/
  | mulVar (prev : Nat) (i : Fin n) : PCStep F n

/-- A PC derivation: a sequence of steps, each producing a polynomial.
    The derivation refutes the formula if the final polynomial is 1. -/
structure PCDerivation (F : Type*) [Field F] (n : Nat) where
  /-- The axiom set. -/
  axioms : PCAXioms F n
  /-- The sequence of derivation steps. -/
  steps : List (PCStep F n)
  /-- The polynomial derived at each step. -/
  derived : List (MvPolynomial (Fin n) F)
  /-- Each step correctly derives its polynomial. -/
  h_valid : ∀ (k : Nat) (hk : k < steps.length),
    match steps[k]'hk with
    | .boolAxiom i => derived[k]? = some (booleanAxiom F n i)
    | .clauseAxiom idx =>
        ∃ p, axioms.clause_polys[idx]? = some p ∧ derived[k]? = some p
    | .add l r =>
        ∃ pl pr, derived[l]? = some pl ∧ derived[r]? = some pr ∧
        derived[k]? = some (pl + pr)
    | .mulVar prev i =>
        ∃ pp, derived[prev]? = some pp ∧
        derived[k]? = some (MvPolynomial.X i * pp)
  /-- The derivation has the same number of derived polynomials as steps. -/
  h_length : derived.length = steps.length
  /-- The final derived polynomial is 1 (refutation). -/
  h_refutes : derived.getLast? = some 1

-- ================================================================
-- Section 4: Degree measure
-- ================================================================

/-- The degree of a PC derivation: the maximum total degree of any
    polynomial appearing in the derivation. -/
noncomputable def PCDerivation.degree {F : Type*} [Field F] {n : Nat}
    (deriv : PCDerivation F n) : Nat :=
  deriv.derived.foldl (fun acc p => max acc (MvPolynomial.totalDegree p)) 0

-- ================================================================
-- Section 5: PC refutability
-- ================================================================

/-- A CNF formula (as a list of clauses on n variables) is
    PC-refutable at degree d over F if there exists a PC derivation
    of degree at most d deriving 1. -/
def PCRefutable (F : Type*) [Field F] (n : Nat)
    (clauses : List (List Int)) (d : Nat) : Prop :=
  ∃ deriv : PCDerivation F n,
    deriv.axioms.clauses = clauses ∧
    deriv.degree ≤ d

-- ================================================================
-- Section 6: Basic lemmas
-- ================================================================

/-- Boolean axioms have degree at most 2. -/
theorem booleanAxiom_degree (F : Type*) [Field F] (n : Nat) (i : Fin n) :
    MvPolynomial.totalDegree (booleanAxiom F n i) ≤ 2 := by
  unfold booleanAxiom
  have h1 : MvPolynomial.totalDegree (MvPolynomial.X (R := F) i ^ 2) ≤ 2 := by
    have := MvPolynomial.totalDegree_pow (MvPolynomial.X (R := F) i) 2
    rw [MvPolynomial.totalDegree_X] at this
    simp
  have h2 : MvPolynomial.totalDegree (MvPolynomial.X (R := F) i) ≤ 2 := by
    rw [MvPolynomial.totalDegree_X]; omega
  have hsub := @MvPolynomial.totalDegree_sub F (Fin n) _
    (MvPolynomial.X (R := F) i ^ 2) (MvPolynomial.X i)
  simp only [ge_iff_le] at *
  omega

/-- The addition rule does not increase degree. -/
theorem add_degree_bound (F : Type*) [Field F] (n : Nat)
    (p q : MvPolynomial (Fin n) F) :
    MvPolynomial.totalDegree (p + q) ≤
      max (MvPolynomial.totalDegree p) (MvPolynomial.totalDegree q) :=
  MvPolynomial.totalDegree_add p q

/-- The multiplication rule increases degree by at most 1. -/
theorem mulVar_degree_bound (F : Type*) [Field F] (n : Nat)
    (p : MvPolynomial (Fin n) F) (i : Fin n) :
    MvPolynomial.totalDegree (MvPolynomial.X i * p) ≤
      MvPolynomial.totalDegree p + 1 := by
  have hmul := MvPolynomial.totalDegree_mul (MvPolynomial.X (R := F) i) p
  rw [MvPolynomial.totalDegree_X] at hmul
  omega

/-- Helper: foldl max is at least acc. -/
theorem foldl_max_ge_acc {α : Type*} (f : α → Nat) (l : List α) (acc : Nat) :
    acc ≤ l.foldl (fun a y => max a (f y)) acc := by
  induction l generalizing acc with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    exact le_trans (Nat.le_max_left _ _) (ih _)

/-- Helper: foldl max tracks the max of the list. -/
theorem foldl_max_mem_ge {α : Type*} (f : α → Nat) (l : List α) (acc : Nat) (x : α)
    (hx : x ∈ l) : f x ≤ l.foldl (fun a y => max a (f y)) acc := by
  induction l generalizing acc with
  | nil => exact absurd hx List.not_mem_nil
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.mem_cons] at *
    cases hx with
    | inl heq =>
      subst heq
      exact le_trans (Nat.le_max_right _ _) (foldl_max_ge_acc f tl _)
    | inr hmem =>
      exact ih (max acc (f hd)) hmem

/-- A PC derivation of degree 0 has all polynomials of degree 0. -/
theorem degree_zero_trivial (F : Type*) [Field F] (n : Nat)
    (deriv : PCDerivation F n)
    (h : deriv.degree = 0) :
    ∀ p ∈ deriv.derived, MvPolynomial.totalDegree p = 0 := by
  intro p hp
  have hle : MvPolynomial.totalDegree p ≤
      deriv.derived.foldl (fun acc q => max acc (MvPolynomial.totalDegree q)) 0 :=
    foldl_max_mem_ge _ deriv.derived 0 p hp
  unfold PCDerivation.degree at h
  omega

/-- Non-vacuity: the empty clause has a degree-0 PC refutation.
    clausePoly F n [] = 1, so the clause axiom for [] directly gives 1. -/
theorem empty_clause_refutable (F : Type*) [Field F] (n : Nat) :
    PCRefutable F n [[]] 0 := by
  have hcp : clausePoly F n [] = (1 : MvPolynomial (Fin n) F) := by
    unfold clausePoly; simp
  -- Build a one-step derivation using clauseAxiom 0
  let axs : PCAXioms F n :=
    { clauses := [[]], clause_polys := [clausePoly F n []], h_clause_correct := rfl }
  let deriv : PCDerivation F n :=
    { axioms := axs
      steps := [.clauseAxiom 0]
      derived := [clausePoly F n []]
      h_valid := fun k hk => by
        have hk0 : k = 0 := by
          simp only [List.length_singleton] at hk; omega
        subst hk0
        simp only [List.getElem_cons_zero]
        exact ⟨clausePoly F n [], rfl, rfl⟩
      h_length := rfl
      h_refutes := by simp [hcp] }
  refine ⟨deriv, rfl, ?_⟩
  show deriv.degree ≤ 0
  unfold PCDerivation.degree
  show List.foldl (fun acc p => max acc (MvPolynomial.totalDegree p)) 0
      [clausePoly F n []] ≤ 0
  simp only [List.foldl_cons, List.foldl_nil]
  rw [hcp, MvPolynomial.totalDegree_one]
  simp

end ClassicalConstraints
