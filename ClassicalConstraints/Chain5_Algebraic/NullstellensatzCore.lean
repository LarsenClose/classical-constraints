/-
  ClassicalConstraints/NullstellensatzCore.lean
  Static Nullstellensatz certificates for SAT unsatisfiability.

  STATUS: 0 sorry. Classical.choice allowed (Side B).
-/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import ClassicalConstraints.Shared.Basic
import ClassicalConstraints.Chain5_Algebraic.PolynomialCalculusCore

namespace ClassicalConstraints

open MvPolynomial

-- ================================================================
-- Section 0: Helper lemmas
-- ================================================================

/-- Each element of zipWith (· * booleanAxiom) is zero when all multipliers are zero. -/
private theorem zipWith_zero_mul_booleanAxiom_eq_zero
    {F : Type*} [Field F] {n : Nat} :
    ∀ (zeros : List (MvPolynomial (Fin n) F)) (idxs : List (Fin n))
      (q : MvPolynomial (Fin n) F),
      (∀ z ∈ zeros, z = (0 : MvPolynomial (Fin n) F)) →
      q ∈ List.zipWith (fun h j => h * booleanAxiom F n j) zeros idxs →
      q = 0 := by
  intro zeros
  induction zeros with
  | nil => intro idxs q _ hq; exact absurd hq List.not_mem_nil
  | cons zhd ztl ih =>
    intro idxs q hzeros hq
    cases idxs with
    | nil => exact absurd hq List.not_mem_nil
    | cons ihd itl =>
      simp only [List.zipWith_cons_cons, List.mem_cons] at hq
      cases hq with
      | inl heq =>
        subst heq
        rw [hzeros zhd (by simp)]
        ring
      | inr hmem =>
        exact ih itl q (fun z hz => hzeros z (List.mem_cons_of_mem _ hz)) hmem

/-- Evaluate a sum of a zipWith; useful for sums of pairs. -/
theorem zipWith_sum_eq_zero_of_snd_zero
    {F : Type*} [Field F] {n : Nat}
    (fms : List (MvPolynomial (Fin n) F))
    (gms : List (MvPolynomial (Fin n) F))
    (a : Fin n → F)
    (h : ∀ g ∈ gms, MvPolynomial.eval a g = 0) :
    MvPolynomial.eval a (List.zipWith (· * ·) fms gms).sum = 0 := by
  induction fms generalizing gms with
  | nil => simp
  | cons fhd ftl ih =>
    cases gms with
    | nil => simp
    | cons ghd gtl =>
      simp only [List.zipWith_cons_cons, List.sum_cons, map_add, map_mul]
      have hghd : MvPolynomial.eval a ghd = 0 := h ghd (by simp)
      rw [hghd, mul_zero, zero_add]
      apply ih
      intro g hg
      exact h g (List.mem_cons_of_mem _ hg)

-- ================================================================
-- Section 1: Nullstellensatz certificates
-- ================================================================

structure NullstellensatzCertificate (F : Type*) [Field F] (n : Nat)
    (clauses : List (List Int)) where
  clause_multipliers : List (MvPolynomial (Fin n) F)
  bool_multipliers : List (MvPolynomial (Fin n) F)
  h_clause_len : clause_multipliers.length = clauses.length
  h_bool_len : bool_multipliers.length = n
  h_identity : (1 : MvPolynomial (Fin n) F) =
    (List.zipWith (· * ·) clause_multipliers (clauses.map (clausePoly F n))).sum +
    (List.zipWith (fun (h : MvPolynomial (Fin n) F) (j : Fin n) => h * booleanAxiom F n j)
      bool_multipliers (List.finRange n)).sum

-- ================================================================
-- Section 2: Degree
-- ================================================================

noncomputable def NullstellensatzCertificate.degree
    {F : Type*} [Field F] {n : Nat} {clauses : List (List Int)}
    (cert : NullstellensatzCertificate F n clauses) : Nat :=
  max
    ((List.zipWith (· * ·) cert.clause_multipliers
      (clauses.map (clausePoly F n))).foldl (fun acc p => max acc (totalDegree p)) 0)
    ((List.zipWith (fun (h : MvPolynomial (Fin n) F) (j : Fin n) => h * booleanAxiom F n j)
      cert.bool_multipliers (List.finRange n)).foldl (fun acc p => max acc (totalDegree p)) 0)

noncomputable def NSDegree (F : Type*) [Field F] (n : Nat)
    (clauses : List (List Int)) : WithTop Nat :=
  ⨅ cert : NullstellensatzCertificate F n clauses, (cert.degree : WithTop Nat)

-- ================================================================
-- Section 3: NS refutability
-- ================================================================

def NSRefutable (F : Type*) [Field F] (n : Nat)
    (clauses : List (List Int)) (d : Nat) : Prop :=
  ∃ cert : NullstellensatzCertificate F n clauses, cert.degree ≤ d

-- ================================================================
-- Section 4: Relationship to PC
-- ================================================================

structure NSFromPC (F : Type*) [Field F] (n : Nat) (clauses : List (List Int)) where
  ns_le_pc : ∀ d, PCRefutable F n clauses d → NSRefutable F n clauses d

-- ================================================================
-- Section 5: Proofs
-- ================================================================

private theorem clausePoly_empty (F : Type*) [Field F] (n : Nat) :
    clausePoly F n [] = (1 : MvPolynomial (Fin n) F) := by unfold clausePoly; simp

/-- Helper: foldl max over a list of zeros is 0. -/
private theorem foldl_max_zero_list {F : Type*} [Field F] {n : Nat}
    (l : List (MvPolynomial (Fin n) F))
    (h : ∀ p ∈ l, p = (0 : MvPolynomial (Fin n) F)) :
    l.foldl (fun acc p => max acc (MvPolynomial.totalDegree p)) 0 = 0 := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.mem_cons] at *
    rw [h hd (Or.inl rfl), MvPolynomial.totalDegree_zero, max_self]
    exact ih (fun p hp => h p (Or.inr hp))

/-- The empty clause is NS-refutable at degree 0. -/
theorem empty_clause_ns_degree_zero (F : Type*) [Field F] (n : Nat) :
    NSRefutable F n [[]] 0 := by
  have hcp : clausePoly F n [] = (1 : MvPolynomial (Fin n) F) := clausePoly_empty F n
  -- bool_multipliers = replicate n 0
  -- clause_multipliers = [1]
  -- Identity: 1 = 1 * clausePoly [] + 0 = 1 * 1 + 0 = 1
  have hbool_sum : (List.zipWith
      (fun (h : MvPolynomial (Fin n) F) (j : Fin n) => h * booleanAxiom F n j)
      (List.replicate n (0 : MvPolynomial (Fin n) F)) (List.finRange n)).sum = 0 := by
    apply List.sum_eq_zero
    intro p hp
    exact zipWith_zero_mul_booleanAxiom_eq_zero _ _ p
      (by intro z hz; simp [List.mem_replicate] at hz; exact hz.2) hp
  refine ⟨⟨[(1 : MvPolynomial (Fin n) F)],
    List.replicate n (0 : MvPolynomial (Fin n) F),
    (by simp), (by simp), ?_⟩, ?_⟩
  · -- h_identity
    simp only [List.map_singleton, List.zipWith_cons_cons, List.zipWith_nil_right,
      hcp, mul_one, List.sum_cons, List.sum_nil, add_zero]
    rw [hbool_sum]; ring
  · -- degree ≤ 0
    unfold NullstellensatzCertificate.degree
    simp only [List.map_singleton, List.zipWith_cons_cons, List.zipWith_nil_right,
      hcp, mul_one, List.foldl_cons, List.foldl_nil, MvPolynomial.totalDegree_one,
      max_self]
    have hbool_zero : (List.zipWith
        (fun (h : MvPolynomial (Fin n) F) (j : Fin n) => h * booleanAxiom F n j)
        (List.replicate n (0 : MvPolynomial (Fin n) F)) (List.finRange n)).foldl
        (fun acc p => max acc (MvPolynomial.totalDegree p)) 0 = 0 := by
      apply foldl_max_zero_list
      intro p hp
      exact zipWith_zero_mul_booleanAxiom_eq_zero _ _ p
        (by intro z hz; simp [List.mem_replicate] at hz; exact hz.2) hp
    rw [hbool_zero]; simp

/-- A certificate of degree 0 means each clause multiplier product has degree 0.
    When the corresponding clause polynomial is nonzero, the multiplier itself has degree 0. -/
theorem degree_zero_constant_multipliers
    {F : Type*} [Field F] {n : Nat} {clauses : List (List Int)}
    (cert : NullstellensatzCertificate F n clauses)
    (h : cert.degree = 0) :
    ∀ (idx : Nat) (hidx : idx < cert.clause_multipliers.length),
      (clauses.map (clausePoly F n))[idx]? ≠ some 0 →
      totalDegree (cert.clause_multipliers[idx]'hidx) = 0 := by
  intro idx hidx hg_nonzero
  unfold NullstellensatzCertificate.degree at h
  have hmax0 : (List.zipWith (· * ·) cert.clause_multipliers
      (clauses.map (clausePoly F n))).foldl
      (fun acc p => max acc (totalDegree p)) 0 = 0 := by omega
  have hidx_map : idx < (clauses.map (clausePoly F n)).length := by
    simp only [List.length_map]; rw [← cert.h_clause_len]; exact hidx
  have hidx_zip : idx < (List.zipWith (· * ·) cert.clause_multipliers
      (clauses.map (clausePoly F n))).length := by
    simp only [List.length_zipWith, List.length_map, ← cert.h_clause_len]
    exact Nat.lt_min.mpr ⟨hidx, hidx⟩
  have hprod_deg : totalDegree ((List.zipWith (· * ·) cert.clause_multipliers
      (clauses.map (clausePoly F n)))[idx]'hidx_zip) = 0 := by
    have hle := foldl_max_mem_ge totalDegree
        (List.zipWith (· * ·) cert.clause_multipliers (clauses.map (clausePoly F n))) 0
        _ (List.getElem_mem hidx_zip)
    rw [hmax0] at hle; omega
  rw [List.getElem_zipWith] at hprod_deg
  have hg : (clauses.map (clausePoly F n))[idx]'hidx_map ≠ 0 := by
    intro heq
    apply hg_nonzero
    simp [List.getElem?_eq_getElem hidx_map, heq]
  by_cases hf : cert.clause_multipliers[idx]'hidx = 0
  · rw [hf, MvPolynomial.totalDegree_zero]
  · have heq := MvPolynomial.totalDegree_mul_of_isDomain (f := cert.clause_multipliers[idx]'hidx)
        (g := (clauses.map (clausePoly F n))[idx]'hidx_map) hf hg
    omega

/-- NS certificate implies unsatisfiability. -/
theorem ns_certificate_implies_unsat
    {F : Type*} [Field F] [CharZero F]
    {n : Nat} {clauses : List (List Int)}
    (cert : NullstellensatzCertificate F n clauses)
    (a : Fin n → F)
    (ha_bool : ∀ i, a i = 0 ∨ a i = 1)
    (hsat : ∀ clause ∈ clauses, MvPolynomial.eval a (clausePoly F n clause) = 0) :
    False := by
  have hid := cert.h_identity
  -- Clause part = 0
  have hclause_zero : MvPolynomial.eval a
      (List.zipWith (· * ·) cert.clause_multipliers (clauses.map (clausePoly F n))).sum = 0 := by
    apply zipWith_sum_eq_zero_of_snd_zero
    intro g hg
    rw [List.mem_map] at hg
    obtain ⟨clause, hclause, hg_eq⟩ := hg
    rw [← hg_eq]
    exact hsat clause hclause
  -- Bool part = 0
  have hbool_zero : MvPolynomial.eval a
      (List.zipWith (fun (h : MvPolynomial (Fin n) F) (j : Fin n) => h * booleanAxiom F n j)
        cert.bool_multipliers (List.finRange n)).sum = 0 := by
    -- Each term is hi * booleanAxiom(ji) = hi * 0 = 0
    -- Prove by induction on the zipWith
    suffices hs : ∀ (bms : List (MvPolynomial (Fin n) F)) (idxs : List (Fin n)),
        MvPolynomial.eval a
          (List.zipWith (fun (h : MvPolynomial (Fin n) F) (j : Fin n) => h * booleanAxiom F n j)
            bms idxs).sum = 0 from hs _ _
    intro bms idxs
    induction bms generalizing idxs with
    | nil => simp
    | cons bhd btl ih =>
      cases idxs with
      | nil => simp
      | cons ihd itl =>
        simp only [List.zipWith_cons_cons, List.sum_cons, map_add, map_mul]
        have hba : MvPolynomial.eval a (booleanAxiom F n ihd) = 0 := by
          unfold booleanAxiom
          simp only [map_sub, map_pow, eval_X]
          rcases ha_bool ihd with h | h <;> simp [h]
        rw [hba, mul_zero, zero_add]
        exact ih itl
  -- 1 = 0 + 0 = 0
  have := congr_arg (MvPolynomial.eval a) hid
  simp only [map_one, map_add] at this
  rw [hclause_zero, hbool_zero] at this
  simp at this

end ClassicalConstraints
