/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

ClassicalConstraints/CSPInstanceCore.lean — Core CSP definitions:
domains, constraint languages, instances, satisfiability.
SAT as an explicit Boolean CSP.

STATUS: 0 sorry, Classical.choice allowed (Side B).
-/

import ClassicalConstraints.Shared.Basic
import ClassicalConstraints.Shared.SATPresheafCore
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic

namespace ClassicalConstraints

-- ════════════════════════════════════════════════════════════
-- Section 1: CSP domain and relations
-- ════════════════════════════════════════════════════════════

/-- A finite domain for CSP, with cardinality at least 2. -/
structure CSPDomain where
  D : Type
  fin : Fintype D
  deceq : DecidableEq D
  card_ge_two : @Fintype.card D fin ≥ 2

/-- A finitary relation: decidable membership, backed by a tuple list. -/
structure FinRelation (D : Type) (deceq : DecidableEq D) (k : Nat) where
  tuples : List (Fin k → D)
  mem : (Fin k → D) → Bool
  mem_iff : ∀ t, mem t = true ↔ t ∈ tuples

-- ════════════════════════════════════════════════════════════
-- Section 2: Constraint language and CSP instance
-- ════════════════════════════════════════════════════════════

/-- A constraint language: a list of relations over a domain. -/
structure ConstraintLanguage (dom : CSPDomain) where
  rels : List (Σ k : Nat, FinRelation dom.D dom.deceq k)
  nonempty : rels.length > 0

/-- A CSP instance over a constraint language. -/
structure CSPInstance (dom : CSPDomain) (lang : ConstraintLanguage dom) where
  num_vars : Nat
  constraints : List (Σ (idx : Fin lang.rels.length),
    Fin (lang.rels[idx].1) → Fin num_vars)

/-- An assignment maps variables to domain values. -/
def CSPInstance.Assignment (dom : CSPDomain)
    {lang : ConstraintLanguage dom}
    (inst : CSPInstance dom lang) : Type :=
  Fin inst.num_vars → dom.D

/-- A single constraint is satisfied by an assignment. -/
def constraintSatisfied (dom : CSPDomain)
    (lang : ConstraintLanguage dom)
    (inst : CSPInstance dom lang)
    (assignment : inst.Assignment dom)
    (c : Σ (idx : Fin lang.rels.length),
      Fin (lang.rels[idx].1) → Fin inst.num_vars) : Bool :=
  (lang.rels[c.1].2).mem (fun i => assignment (c.2 i))

/-- An assignment satisfies a CSP instance. -/
def CSPInstance.isSatisfied (dom : CSPDomain)
    (lang : ConstraintLanguage dom)
    (inst : CSPInstance dom lang)
    (assignment : inst.Assignment dom) : Bool :=
  inst.constraints.all (constraintSatisfied dom lang inst assignment)

/-- A CSP instance is satisfiable. -/
def CSPInstance.Satisfiable (dom : CSPDomain)
    (lang : ConstraintLanguage dom)
    (inst : CSPInstance dom lang) : Prop :=
  ∃ a : inst.Assignment dom, inst.isSatisfied dom lang a = true

/-- A CSP family indexed by size. -/
def CSPFamily (dom : CSPDomain) (lang : ConstraintLanguage dom) :=
  Nat → CSPInstance dom lang

-- ════════════════════════════════════════════════════════════
-- Section 3: Boolean domain
-- ════════════════════════════════════════════════════════════

/-- The Boolean domain. -/
def boolDomain : CSPDomain where
  D := Bool
  fin := inferInstance
  deceq := inferInstance
  card_ge_two := by decide

/-- A clause as a Boolean relation. -/
structure BoolClause (k : Nat) where
  polarity : Fin k → Bool

/-- Evaluate a clause on a Boolean tuple. -/
def BoolClause.eval {k : Nat} (c : BoolClause k) (t : Fin k → Bool) : Bool :=
  (List.finRange k).any (fun i =>
    if c.polarity i then t i else !t i)

-- ════════════════════════════════════════════════════════════
-- Section 4: Boolean tuple enumeration
-- ════════════════════════════════════════════════════════════

/-- Enumerate all functions Fin k → Bool. -/
private def allBoolTuples : (k : Nat) → List (Fin k → Bool)
  | 0 => [Fin.elim0]
  | k + 1 =>
    (allBoolTuples k).flatMap (fun t =>
      [ (fun i => if h : i.val < k then t ⟨i.val, h⟩ else false),
        (fun i => if h : i.val < k then t ⟨i.val, h⟩ else true) ])

private theorem allBoolTuples_mem : ∀ (k : Nat) (t : Fin k → Bool), t ∈ allBoolTuples k := by
  intro k
  induction k with
  | zero =>
    intro t
    simp only [allBoolTuples, List.mem_singleton]
    funext i; exact Fin.elim0 i
  | succ n ih =>
    intro t
    simp only [allBoolTuples, List.mem_flatMap, List.mem_cons, List.mem_nil_iff, or_false]
    refine ⟨fun i => t (Fin.castSucc i), ih _, ?_⟩
    by_cases hn : t ⟨n, Nat.lt_succ_self n⟩
    · right
      funext i
      by_cases hi : i.val < n
      · simp only [dif_pos hi]
        have heq : (Fin.castSucc ⟨i.val, hi⟩ : Fin (n + 1)) = i := Fin.ext rfl
        rw [heq]
      · simp only [dif_neg hi]
        have hieqn : i = ⟨n, Nat.lt_succ_self n⟩ :=
          Fin.ext (Nat.le_antisymm (Nat.lt_succ_iff.mp i.isLt) (Nat.not_lt.mp hi))
        rw [hieqn]; exact hn
    · left
      funext i
      by_cases hi : i.val < n
      · simp only [dif_pos hi]
        have heq : (Fin.castSucc ⟨i.val, hi⟩ : Fin (n + 1)) = i := Fin.ext rfl
        rw [heq]
      · simp only [dif_neg hi]
        have hieqn : i = ⟨n, Nat.lt_succ_self n⟩ :=
          Fin.ext (Nat.le_antisymm (Nat.lt_succ_iff.mp i.isLt) (Nat.not_lt.mp hi))
        rw [hieqn]
        simp only [Bool.not_eq_true] at hn; exact hn

/-- Build a FinRelation for a BoolClause of arity k. -/
def boolClauseRelation (k : Nat) (c : BoolClause k) :
    FinRelation Bool instDecidableEqBool k where
  tuples := (allBoolTuples k).filter (fun t => c.eval t)
  mem := c.eval
  mem_iff := by
    intro t; simp only [List.mem_filter]
    exact ⟨fun h => ⟨allBoolTuples_mem k t, h⟩, fun ⟨_, h⟩ => h⟩

-- ════════════════════════════════════════════════════════════
-- Section 5: SAT clause relation
-- ════════════════════════════════════════════════════════════

/-- Build a FinRelation of arity n for a single SAT clause.
    mem = clauseSatisfied directly. -/
def satClauseRel (φ : SATInstance) (clause : List Int) :
    FinRelation Bool instDecidableEqBool φ.num_vars where
  tuples := (allBoolTuples φ.num_vars).filter (fun t => φ.clauseSatisfied t clause)
  mem := fun t => φ.clauseSatisfied t clause
  mem_iff := by
    intro t; simp only [List.mem_filter]
    exact ⟨fun h => ⟨allBoolTuples_mem _ t, h⟩, fun ⟨_, h⟩ => h⟩

-- ════════════════════════════════════════════════════════════
-- Section 6: SAT → CSP translation
-- ════════════════════════════════════════════════════════════

/-- Trivial 0-ary relation (always true). -/
private def trivialRel : FinRelation Bool instDecidableEqBool 0 where
  tuples := [Fin.elim0]
  mem := fun _ => true
  mem_iff := by
    intro t; simp only [List.mem_singleton]
    exact ⟨fun _ => funext (fun i => i.elim0), fun _ => trivial⟩

-- The SAT language when clauses are nonempty.
-- All relations have arity φ.num_vars; the i-th relation is satClauseRel for clause i.
-- The CSP language for a SATInstance (nonempty clauses).
-- rels is the map of clauses to satClauseRel relations.
private def satCSPLang (φ : SATInstance) (h : 0 < φ.clauses.length) :
    ConstraintLanguage boolDomain :=
  { rels := φ.clauses.map (fun clause => ⟨φ.num_vars, satClauseRel φ clause⟩)
    nonempty := by simp [List.length_map, h] }

-- rels.length of satCSPLang equals φ.clauses.length.
private theorem satCSPLang_length (φ : SATInstance) (h : 0 < φ.clauses.length) :
    (satCSPLang φ h).rels.length = φ.clauses.length := by
  simp [satCSPLang, List.length_map]

-- Getelem of satCSPLang at index i (nat index, with separate bound proofs).
private theorem satCSPLang_getElem (φ : SATInstance) (h : 0 < φ.clauses.length)
    (i : Nat) (hi : i < φ.clauses.length)
    (hi' : i < (satCSPLang φ h).rels.length) :
    (satCSPLang φ h).rels[i]'hi' =
    ⟨φ.num_vars, satClauseRel φ (φ.clauses[i]'hi)⟩ := by
  simp [satCSPLang, List.getElem_map]

-- Arity at nat index i is φ.num_vars.
private theorem satCSPLang_arity_nat (φ : SATInstance) (h : 0 < φ.clauses.length)
    (i : Nat) (hi : i < φ.clauses.length) (hi' : i < (satCSPLang φ h).rels.length) :
    ((satCSPLang φ h).rels[i]'hi').1 = φ.num_vars := by
  rw [satCSPLang_getElem φ h i hi hi']

-- The Fin index for clause ci in satCSPLang.
private def satRelIdx (φ : SATInstance) (h : 0 < φ.clauses.length)
    (ci : Fin φ.clauses.length) : Fin (satCSPLang φ h).rels.length :=
  Fin.cast (satCSPLang_length φ h).symm ci

-- satRelIdx.val = ci.val.
private theorem satRelIdx_val (φ : SATInstance) (h : 0 < φ.clauses.length)
    (ci : Fin φ.clauses.length) : (satRelIdx φ h ci).val = ci.val := rfl

-- Arity at Fin index ci is φ.num_vars.
private theorem satCSPLang_arity (φ : SATInstance) (h : 0 < φ.clauses.length)
    (ci : Fin φ.clauses.length) :
    (satCSPLang φ h).rels[satRelIdx φ h ci].1 = φ.num_vars :=
  satCSPLang_arity_nat φ h ci.val ci.isLt _

-- HEq between rels[satRelIdx ci].2 and satClauseRel φ clause_i.
-- Used to transfer mem equalities.
private theorem satCSPLang_rel_heq (φ : SATInstance) (h : 0 < φ.clauses.length)
    (ci : Fin φ.clauses.length) :
    HEq ((satCSPLang φ h).rels[satRelIdx φ h ci].2)
        (satClauseRel φ (φ.clauses[ci.val]'ci.isLt)) := by
  have heq : (satCSPLang φ h).rels[satRelIdx φ h ci] =
      ⟨φ.num_vars, satClauseRel φ (φ.clauses[ci.val]'ci.isLt)⟩ :=
    satCSPLang_getElem φ h ci.val ci.isLt _
  exact (Sigma.mk.inj heq).2

/-- Convert a SATInstance to a Boolean CSP.
    Each clause becomes a relation of arity φ.num_vars with identity scope. -/
def satToCSP (φ : SATInstance) :
    Σ (lang : ConstraintLanguage boolDomain), CSPInstance boolDomain lang :=
  if h : 0 < φ.clauses.length then
    let lang := satCSPLang φ h
    -- Build constraint for each clause: relation index j = satRelIdx, scope = Fin.cast.
    let mkConstraint (ci : Fin φ.clauses.length) :
        Σ idx : Fin lang.rels.length, Fin (lang.rels[idx].1) → Fin φ.num_vars :=
      let j : Fin lang.rels.length := satRelIdx φ h ci
      let harity : lang.rels[j].1 = φ.num_vars := satCSPLang_arity φ h ci
      ⟨j, fun i => Fin.cast harity i⟩
    ⟨lang, { num_vars := φ.num_vars, constraints := List.ofFn mkConstraint }⟩
  else
    ⟨{ rels := [⟨0, trivialRel⟩], nonempty := by simp },
     { num_vars := φ.num_vars, constraints := [] }⟩

-- ════════════════════════════════════════════════════════════
-- Section 7: Core theorems
-- ════════════════════════════════════════════════════════════

/-- The Boolean domain has exactly 2 elements. -/
theorem boolDomain_card : @Fintype.card boolDomain.D boolDomain.fin = 2 := by
  decide

/-- Every 1-element domain is impossible given card_ge_two. -/
theorem one_element_trivial (dom : CSPDomain)
    (h : @Fintype.card dom.D dom.fin = 1) : False := by
  have := dom.card_ge_two; omega

-- ════════════════════════════════════════════════════════════
-- Section 8: SAT ↔ CSP equivalence
-- ════════════════════════════════════════════════════════════

-- Key: the constraint for clause ci checks clauseSatisfied.
-- Approach: use the Sigma equality to transport the motive.
-- The motive is parametric in the Sigma element s:
--   M s := ∀ (h_ar : s.1 = φ.num_vars), s.2.mem (fun i => a (Fin.cast h_ar i)) = φ.clauseSatisfied a clause_i
-- We prove M ⟨φ.num_vars, satClauseRel φ clause_i⟩ easily (h_ar = rfl, Fin.cast rfl = id),
-- then transport via the Sigma equality hsig.symm.
private theorem satToCSP_constraint_iff (φ : SATInstance) (h : 0 < φ.clauses.length)
    (ci : Fin φ.clauses.length) (a : Fin φ.num_vars → Bool) :
    let lang := satCSPLang φ h
    let j : Fin lang.rels.length := satRelIdx φ h ci
    let harity : lang.rels[j].1 = φ.num_vars := satCSPLang_arity φ h ci
    lang.rels[j].2.mem (fun i => a (Fin.cast harity i)) =
    φ.clauseSatisfied a (φ.clauses.get ci) := by
  -- Compute the Sigma equality.
  have hsig : (satCSPLang φ h).rels[satRelIdx φ h ci] =
      ⟨φ.num_vars, satClauseRel φ (φ.clauses[ci.val]'ci.isLt)⟩ :=
    satCSPLang_getElem φ h ci.val ci.isLt _
  -- Define the motive parametric in s.
  -- M s h_ar = s.2.mem (fun i => a (Fin.cast h_ar i)) = clauseSatisfied a clause_i
  -- Prove M ⟨φ.num_vars, satClauseRel φ clause_i⟩ rfl.
  -- Transport via hsig.symm to get M rels[j] (satCSPLang_arity φ h ci).
  suffices ∀ (s : Σ k : Nat, FinRelation Bool instDecidableEqBool k)
      (hs : s = ⟨φ.num_vars, satClauseRel φ (φ.clauses[ci.val]'ci.isLt)⟩)
      (h_ar : s.1 = φ.num_vars),
      s.2.mem (fun i => a (Fin.cast h_ar i)) = φ.clauseSatisfied a (φ.clauses.get ci) by
    exact this _ hsig (satCSPLang_arity φ h ci)
  intro s hs h_ar
  -- Now s = ⟨φ.num_vars, satClauseRel φ clause_i⟩ and h_ar : s.1 = φ.num_vars.
  subst hs
  -- s is now the concrete value; h_ar : φ.num_vars = φ.num_vars.
  -- Fin.cast h_ar = id (both sides are φ.num_vars).
  simp [satClauseRel, List.get_eq_getElem]

-- Helpers for satToCSP projections.
private theorem satToCSP_fst_pos (φ : SATInstance) (h : 0 < φ.clauses.length) :
    (satToCSP φ).1 = satCSPLang φ h := by
  unfold satToCSP; rw [dif_pos h]

private theorem satToCSP_snd_num_vars_pos (φ : SATInstance) (h : 0 < φ.clauses.length) :
    (satToCSP φ).2.num_vars = φ.num_vars := by
  unfold satToCSP; rw [dif_pos h]

/-- SAT satisfiability iff CSP satisfiability under satToCSP. -/
theorem sat_csp_equivalence (φ : SATInstance) :
    φ.Satisfiable ↔ (satToCSP φ).2.Satisfiable boolDomain (satToCSP φ).1 := by
  by_cases hempty : 0 < φ.clauses.length
  · -- Nonempty clauses. Reduce satToCSP to its concrete branch using dif_pos.
    have hsat_eq : satToCSP φ =
        ⟨satCSPLang φ hempty,
         { num_vars := φ.num_vars,
           constraints := List.ofFn (fun ci : Fin φ.clauses.length =>
             ⟨satRelIdx φ hempty ci,
              fun i => Fin.cast (satCSPLang_arity φ hempty ci) i⟩) }⟩ := by
      unfold satToCSP; rw [dif_pos hempty]
    rw [hsat_eq]
    simp only [SATInstance.Satisfiable, SATInstance.instanceSatisfied, List.all_eq_true,
               CSPInstance.Satisfiable, CSPInstance.isSatisfied]
    -- Now both assignments are Fin φ.num_vars → Bool.
    constructor
    · intro ⟨a, ha⟩
      refine ⟨a, ?_⟩
      intro c hc
      simp only [List.mem_ofFn] at hc
      obtain ⟨ci, hci⟩ := hc
      subst hci
      simp only [constraintSatisfied]
      rw [satToCSP_constraint_iff φ hempty ci a]
      exact ha _ (List.getElem_mem ci.isLt)
    · intro ⟨a, ha⟩
      refine ⟨a, ?_⟩
      intro clause hclause
      obtain ⟨ci, hci⟩ := List.mem_iff_get.mp hclause
      -- Apply ha to the constraint corresponding to clause ci.
      have hsat := ha ⟨satRelIdx φ hempty ci, fun i => Fin.cast (satCSPLang_arity φ hempty ci) i⟩ (by
        simp only [List.mem_ofFn]
        exact ⟨ci, rfl⟩)
      simp only [constraintSatisfied] at hsat
      rw [satToCSP_constraint_iff φ hempty ci a] at hsat
      rw [List.get_eq_getElem] at hci
      rwa [← hci]
  · -- Empty clauses: both sides trivially satisfied.
    have hsat_eq : satToCSP φ =
        ⟨{ rels := [⟨0, trivialRel⟩], nonempty := by simp },
         { num_vars := φ.num_vars, constraints := [] }⟩ := by
      unfold satToCSP; rw [dif_neg hempty]
    rw [hsat_eq]
    simp only [SATInstance.Satisfiable, SATInstance.instanceSatisfied, List.all_eq_true,
               CSPInstance.Satisfiable, CSPInstance.isSatisfied]
    constructor
    · intro ⟨a, _⟩; exact ⟨a, fun x hc => by exact absurd hc (List.not_mem_nil (a := x))⟩
    · intro _
      exact ⟨fun _ => false, fun clause hclause =>
        absurd (List.length_pos_of_mem hclause) (by omega)⟩

end ClassicalConstraints
