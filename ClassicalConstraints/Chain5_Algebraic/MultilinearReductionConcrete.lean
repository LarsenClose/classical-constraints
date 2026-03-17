/-
  ClassicalConstraints/MultilinearReductionConcrete.lean
  Concrete multilinear reduction on MvPolynomial: projects polynomials
  to the multilinear fragment by capping each variable exponent at 1.

  This provides the concrete mathematical content behind
  MultilinearReduction (defined in AlgebraicProofLock.lean):
  1. The reduction produces multilinear polynomials (exponents ≤ 1)
  2. The reduction is degree-non-increasing (totalDegree)
  3. Evaluation at Boolean points is invariant under reduction

  These three facts close MultilinearCofinality for the algebraic
  proof complexity model (Chain 5).

  STATUS: Classical.choice allowed (Side B).
-/

import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Finsupp.Basic

namespace ClassicalConstraints

open MvPolynomial

-- ================================================================
-- Section 1: Exponent capping
-- ================================================================

/-- Cap each exponent at 1: the syntactic multilinear projection on
    exponent vectors. For e = (e₁, e₂, ..., eₙ), capExp e = (min e₁ 1, min e₂ 1, ...). -/
noncomputable def capExp {σ : Type*} (e : σ →₀ ℕ) : σ →₀ ℕ :=
  e.mapRange (fun x => min x 1) (by simp)

@[simp]
theorem capExp_apply {σ : Type*} (e : σ →₀ ℕ) (i : σ) :
    capExp e i = min (e i) 1 := by
  unfold capExp; exact Finsupp.mapRange_apply ..

theorem capExp_le {σ : Type*} (e : σ →₀ ℕ) (i : σ) :
    capExp e i ≤ e i := by
  rw [capExp_apply]; exact Nat.min_le_left _ _

theorem capExp_le_one {σ : Type*} (e : σ →₀ ℕ) (i : σ) :
    capExp e i ≤ 1 := by
  rw [capExp_apply]; exact Nat.min_le_right _ _

theorem capExp_idempotent {σ : Type*} (e : σ →₀ ℕ) :
    capExp (capExp e) = capExp e := by
  ext i; simp [capExp_apply]

/-- capExp preserves support: i has a nonzero exponent iff min(eᵢ, 1) ≠ 0. -/
theorem capExp_support {σ : Type*} (e : σ →₀ ℕ) :
    (capExp e).support = e.support := by
  ext i
  simp only [Finsupp.mem_support_iff, capExp_apply]
  omega

-- ================================================================
-- Section 2: Multilinear reduction on MvPolynomial
-- ================================================================

/-- Multilinear reduction: cap all exponents at 1.
    Maps each monomial c * ∏ xᵢ^eᵢ to c * ∏ xᵢ^(min eᵢ 1).
    When two monomials collapse to the same multilinear monomial,
    their coefficients are added. -/
noncomputable def multilinearReduce {F : Type*} [CommSemiring F]
    {σ : Type*} [DecidableEq σ]
    (p : MvPolynomial σ F) : MvPolynomial σ F :=
  Finsupp.mapDomain capExp p

-- ================================================================
-- Section 3: Multilinearity of the output
-- ================================================================

/-- Every exponent in the support of multilinearReduce p is ≤ 1. -/
theorem multilinearReduce_exponents_le_one {F : Type*} [CommSemiring F]
    {σ : Type*} [DecidableEq σ]
    (p : MvPolynomial σ F)
    (e : σ →₀ ℕ) (he : e ∈ (multilinearReduce p).support)
    (i : σ) : e i ≤ 1 := by
  unfold multilinearReduce at he
  have hsub := Finsupp.mapDomain_support he
  rw [Finset.mem_image] at hsub
  obtain ⟨e', _, rfl⟩ := hsub
  exact capExp_le_one e' i

-- ================================================================
-- Section 4: Degree bound
-- ================================================================

/-- The sum of capped exponents is at most the sum of original exponents. -/
theorem capExp_degree_le {σ : Type*} (e : σ →₀ ℕ) :
    (capExp e).sum (fun _ k => k) ≤ e.sum (fun _ k => k) := by
  unfold Finsupp.sum
  rw [capExp_support]
  apply Finset.sum_le_sum
  intro i _
  exact capExp_le e i

/-- Multilinear reduction is degree-non-increasing. -/
theorem multilinearReduce_totalDegree_le {F : Type*} [CommSemiring F]
    {σ : Type*} [DecidableEq σ]
    (p : MvPolynomial σ F) :
    totalDegree (multilinearReduce p) ≤ totalDegree p := by
  unfold totalDegree multilinearReduce
  apply Finset.sup_le
  intro e he
  have hsub := Finsupp.mapDomain_support he
  rw [Finset.mem_image] at hsub
  obtain ⟨e', he', rfl⟩ := hsub
  exact le_trans (capExp_degree_le e')
    (Finset.le_sup (f := fun s => s.sum (fun _ k => k)) he')

-- ================================================================
-- Section 5: Boolean evaluation invariance
-- ================================================================

/-- For idempotent elements (a² = a), all positive powers equal a. -/
theorem idempotent_pow {R : Type*} [Monoid R] (a : R) (h : a ^ 2 = a)
    (k : ℕ) (hk : k ≥ 1) : a ^ k = a := by
  induction k with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => simp
    | succ m =>
      rw [pow_succ, ih (by omega)]
      have : a * a = a := by rw [← sq, h]
      exact this

/-- The Finsupp product over capExp equals the original product at Boolean points.
    Uses the fact that aᵢ^(min k 1) = aᵢ^k when aᵢ² = aᵢ. -/
theorem capExp_prod_eq {σ : Type*} {F : Type*} [CommMonoidWithZero F]
    (e : σ →₀ ℕ) (a : σ → F)
    (ha : ∀ i, a i ^ 2 = a i) :
    (capExp e).prod (fun i k => a i ^ k) = e.prod (fun i k => a i ^ k) := by
  unfold Finsupp.prod
  rw [capExp_support]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Finsupp.mem_support_iff] at hi
  have hge : e i ≥ 1 := Nat.one_le_iff_ne_zero.mpr hi
  show a i ^ (capExp e i) = a i ^ (e i)
  rw [capExp_apply, Nat.min_eq_right hge, pow_one,
      idempotent_pow (a i) (ha i) (e i) hge]

/-- Evaluation at Boolean points is invariant under multilinear reduction.

    The key semantic fact: for any assignment a with aᵢ² = aᵢ (Boolean),
    evaluating p and multilinearReduce(p) at a gives the same result.
    This is because x^k = x on {0,1} for k ≥ 1: capping exponents
    at 1 does not change the polynomial's value at Boolean points. -/
theorem multilinearReduce_eval_eq {F : Type*} [CommSemiring F]
    {σ : Type*} [DecidableEq σ]
    (p : MvPolynomial σ F) (a : σ → F)
    (ha : ∀ i, a i ^ 2 = a i) :
    MvPolynomial.eval a (multilinearReduce p) = MvPolynomial.eval a p := by
  -- Both sides are R-algebra homomorphism values. Decompose p as a sum
  -- of monomials and show each monomial's eval is preserved by capExp.
  simp only [multilinearReduce, MvPolynomial.eval]
  simp only [Finsupp.mapDomain, Finsupp.sum]
  rw [map_sum]
  conv_rhs => rw [← Finsupp.sum_single p, Finsupp.sum, map_sum]
  apply Finset.sum_congr rfl
  intro e _
  change (eval₂Hom (RingHom.id F) a) (monomial (capExp e) (p.toFun e)) =
         (eval₂Hom (RingHom.id F) a) (monomial e (p.toFun e))
  simp only [eval₂Hom_monomial, RingHom.id_apply]
  congr 1
  exact capExp_prod_eq e a ha

end ClassicalConstraints
