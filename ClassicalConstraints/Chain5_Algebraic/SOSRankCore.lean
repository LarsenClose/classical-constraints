/-
  ClassicalConstraints/SOSRankCore.lean
  Sum-of-Squares (SoS) / Positivstellensatz / Lasserre hierarchy
  for refuting SAT instances.

  SoS at degree 2d exhibits:
    -1 = sum_i s_i * g_i + sum_j t_j * (x_j - x_j^2) + sigma
  where s_i, t_j, sigma are bounded-degree SoS polynomials.

  Works over ordered fields (Field + LinearOrder + IsStrictOrderedRing).
  Over GF(2) or other finite fields, SoS is meaningless.

  STATUS: 0 sorry. Classical.choice allowed (Side B).
-/

import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Choose.Bounds
import ClassicalConstraints.Shared.Basic
import ClassicalConstraints.Chain5_Algebraic.PolynomialCalculusCore
import ClassicalConstraints.Chain5_Algebraic.NullstellensatzCore

namespace ClassicalConstraints

open MvPolynomial

-- ================================================================
-- Section 1: Sum of squares polynomials
-- ================================================================

/-- A polynomial is a sum of squares (SoS) if it can be written as
    sum_i p_i^2 for some polynomials p_i. -/
structure IsSumOfSquares (F : Type*) [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (n : Nat) (p : MvPolynomial (Fin n) F) where
  /-- The square summands. -/
  summands : List (MvPolynomial (Fin n) F)
  /-- The polynomial equals the sum of squares. -/
  h_eq : p = (summands.map (· ^ 2)).sum

/-- A bounded-degree SoS polynomial: sum of squares where each
    summand has degree at most d. -/
structure BoundedSoS (F : Type*) [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (n : Nat) (d : Nat) (p : MvPolynomial (Fin n) F) extends IsSumOfSquares F n p where
  /-- Each summand has degree at most d. -/
  h_degree : ∀ q ∈ summands, totalDegree q ≤ d

-- ================================================================
-- Section 2: SoS refutation
-- ================================================================

/-- An SoS refutation of degree 2d for a CNF formula.
    Witnesses: -1 = sum_i s_i * g_i + sum_j t_j * b_j + sigma
    where:
    - g_i are clause polynomials
    - b_j = x_j - x_j^2 (Boolean constraints)
    - s_i are degree-d SoS polynomials (one per clause)
    - t_j are arbitrary polynomials of degree <= 2*d
    - sigma is a degree-d SoS polynomial -/
structure SoSRefutation (F : Type*) [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (n : Nat) (clauses : List (List Int)) (d : Nat) where
  /-- SoS multipliers for clause polynomials. -/
  clause_sos : List (MvPolynomial (Fin n) F)
  /-- Each clause multiplier is SoS with bounded degree. -/
  clause_sos_bounded : ∀ (i : Nat) (hi : i < clause_sos.length),
    BoundedSoS F n d (clause_sos[i]'hi)
  /-- Multipliers for Boolean constraints. -/
  bool_multipliers : List (MvPolynomial (Fin n) F)
  /-- Boolean multipliers have bounded degree. -/
  bool_degree_bounded : ∀ (j : Nat) (hj : j < bool_multipliers.length),
    totalDegree (bool_multipliers[j]'hj) ≤ 2 * d
  /-- The "free" SoS term sigma. -/
  sigma : MvPolynomial (Fin n) F
  /-- sigma is SoS with bounded degree. -/
  sigma_sos : BoundedSoS F n d sigma
  /-- Length matching. -/
  h_clause_len : clause_sos.length = clauses.length
  h_bool_len : bool_multipliers.length = n
  /-- The Positivstellensatz identity. -/
  h_identity : (-1 : MvPolynomial (Fin n) F) =
    (List.zipWith (· * ·) clause_sos (clauses.map (clausePoly F n))).sum +
    (List.zipWith (fun h (j : Fin n) => h * (X j - X j ^ 2))
      bool_multipliers (List.finRange n)).sum +
    sigma

-- ================================================================
-- Section 3: SoS degree and refutability
-- ================================================================

/-- The SoS degree of a refutation is 2d. -/
def SoSRefutation.sosDegree {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {n : Nat} {clauses : List (List Int)} {d : Nat}
    (_ref : SoSRefutation F n clauses d) : Nat := 2 * d

/-- A formula is SoS-refutable at degree 2d. -/
def SoSRefutable (F : Type*) [Field F] [LinearOrder F] [IsStrictOrderedRing F] (n : Nat)
    (clauses : List (List Int)) (d : Nat) : Prop :=
  Nonempty (SoSRefutation F n clauses d)

-- ================================================================
-- Section 4: Moment matrix formulation (alternative)
-- ================================================================

/-- The moment matrix approach: at degree d, the moment matrix
    M[alpha, beta] = y_{alpha + beta} must be PSD.
    Number of monomials of degree <= d in n variables is C(n+d, d). -/
structure MomentFormulation (n : Nat) (d : Nat) where
  /-- Number of monomials of degree <= d in n variables. -/
  num_monomials : Nat
  /-- The moment matrix size equals C(n+d, d). -/
  h_size : num_monomials = Nat.choose (n + d) d

-- ================================================================
-- Section 5: Relationship to PC and NS
-- ================================================================

/-- SoS is at least as strong as NS: any NS certificate of degree d
    can be converted to an SoS refutation at the same degree.
    (Constants are trivially SoS.) -/
structure SoSFromNS where
  ns_implies_sos : ∀ (F : Type*) [Field F] [LinearOrder F] [IsStrictOrderedRing F] (n : Nat)
    (clauses : List (List Int)) (d : Nat),
    NSRefutable F n clauses d → SoSRefutable F n clauses d

/-- SoS at degree 2d can simulate PC at degree d. -/
structure PCToSoS where
  pc_to_sos : ∀ (F : Type*) [Field F] [LinearOrder F] [IsStrictOrderedRing F] (n : Nat)
    (clauses : List (List Int)) (d : Nat),
    PCRefutable F n clauses d → SoSRefutable F n clauses d

-- ================================================================
-- Section 6: Concrete lower bound families
-- ================================================================

/-- A well-formed SAT family: all literal indices are in bounds. -/
def WellFormedFamily (num_vars : Nat) (clauses : List (List Int)) : Prop :=
  ∀ clause ∈ clauses, ∀ lit ∈ clause,
    (lit > 0 → lit.toNat - 1 < num_vars) ∧
    (lit < 0 → (-lit).toNat - 1 < num_vars)

/-- A family of unsatisfiable formulas with SoS degree lower bounds. -/
structure SoSHardFamily where
  /-- The formula family: (num_vars, clauses) at each size. -/
  family : Nat → (Nat × List (List Int))
  /-- All instances are well-formed. -/
  h_wf : ∀ n, WellFormedFamily (family n).1 (family n).2
  /-- All instances are unsatisfiable (via Boolean evaluation):
      no Boolean assignment satisfies all clauses. -/
  h_unsat : ∀ n, ∀ (a : Fin (family n).1 → Bool),
    ∃ clause ∈ (family n).2, ∀ lit ∈ clause,
      (lit > 0 → ∃ h : lit.toNat - 1 < (family n).1, a ⟨lit.toNat - 1, h⟩ = false) ∧
      (lit < 0 → ∃ h : (-lit).toNat - 1 < (family n).1, a ⟨(-lit).toNat - 1, h⟩ = true)
  /-- The number of variables grows. -/
  h_growing : ∀ n, (family n).1 ≥ n
  /-- SoS degree lower bound. -/
  degree_lower_bound : Nat → Nat
  /-- The lower bound is at least linear. -/
  h_lb_linear : ∃ c > 0, ∀ n, degree_lower_bound n ≥ c * n
  /-- The lower bound holds over any ordered field. -/
  h_hard : ∀ (F : Type*) [Field F] [LinearOrder F] [IsStrictOrderedRing F] (n d : Nat),
    d < degree_lower_bound n →
    ¬SoSRefutable F (family n).1 (family n).2 d

-- ================================================================
-- Section 7: Proofs
-- ================================================================

/-- A sum of squares evaluates to a nonneg value over an ordered field. -/
theorem sos_eval_nonneg {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {n : Nat} {p : MvPolynomial (Fin n) F}
    (sos : IsSumOfSquares F n p) (a : Fin n → F) :
    0 ≤ MvPolynomial.eval a p := by
  rw [sos.h_eq]
  simp only [map_list_sum, List.map_map]
  apply List.sum_nonneg
  intro q hq
  simp only [List.mem_map, Function.comp] at hq
  obtain ⟨s, _, rfl⟩ := hq
  rw [map_pow]
  exact sq_nonneg _

/-- SoS refutations are sound: if an SoS refutation exists for a formula,
    the formula is unsatisfiable over {0,1}^n.

    Proof: Evaluate the identity at a Boolean assignment a.
    - sigma(a) >= 0 (sum of squares over an ordered field)
    - x_j(1-x_j) = 0 for Boolean x_j, so Boolean terms vanish
    - s_i(a) >= 0 (SoS), clause terms vanish if all clauses satisfied
    - RHS >= 0 but LHS = -1 < 0. Contradiction. -/
theorem sos_implies_unsat {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {n : Nat} {clauses : List (List Int)} {d : Nat}
    (ref : SoSRefutation F n clauses d)
    (a : Fin n → F)
    (ha : ∀ i, a i = 0 ∨ a i = 1)
    (hsat : ∀ clause ∈ clauses, MvPolynomial.eval a (clausePoly F n clause) = 0) :
    False := by
  have hid := ref.h_identity
  -- Clause part evaluates to 0
  have hclause_zero : MvPolynomial.eval a
      (List.zipWith (· * ·) ref.clause_sos (clauses.map (clausePoly F n))).sum = 0 := by
    apply zipWith_sum_eq_zero_of_snd_zero
    intro g hg
    rw [List.mem_map] at hg
    obtain ⟨clause, hclause, hg_eq⟩ := hg
    rw [← hg_eq]
    exact hsat clause hclause
  -- Boolean part evaluates to 0 (x_j - x_j^2 = 0 on {0,1})
  have hbool_zero : MvPolynomial.eval a
      (List.zipWith (fun h (j : Fin n) => h * (X j - X j ^ 2))
        ref.bool_multipliers (List.finRange n)).sum = 0 := by
    suffices hs : ∀ (bms : List (MvPolynomial (Fin n) F)) (idxs : List (Fin n)),
        MvPolynomial.eval a
          (List.zipWith (fun h (j : Fin n) => h * (X j - X j ^ 2)) bms idxs).sum = 0
      from hs _ _
    intro bms idxs
    induction bms generalizing idxs with
    | nil => simp
    | cons bhd btl ih =>
      cases idxs with
      | nil => simp
      | cons ihd itl =>
        simp only [List.zipWith_cons_cons, List.sum_cons, map_add, map_mul, map_sub, map_pow,
          eval_X]
        have hbool_val : a ihd - a ihd ^ 2 = 0 := by
          rcases ha ihd with h | h <;> simp [h]
        rw [hbool_val, mul_zero, zero_add]
        exact ih itl
  -- sigma evaluates to >= 0
  have hsigma_nonneg : 0 ≤ MvPolynomial.eval a ref.sigma :=
    sos_eval_nonneg ref.sigma_sos.toIsSumOfSquares a
  -- RHS = 0 + 0 + sigma >= 0, but LHS = -1 < 0. Contradiction.
  have hrhs_nonneg : 0 ≤ MvPolynomial.eval a
      ((List.zipWith (· * ·) ref.clause_sos (clauses.map (clausePoly F n))).sum +
      (List.zipWith (fun h (j : Fin n) => h * (X j - X j ^ 2))
        ref.bool_multipliers (List.finRange n)).sum +
      ref.sigma) := by
    simp only [map_add]
    rw [hclause_zero, hbool_zero, zero_add, zero_add]
    exact hsigma_nonneg
  have := congr_arg (MvPolynomial.eval a) hid
  simp only [map_neg, map_one] at this
  linarith [hrhs_nonneg]

/-- SoS degree is monotone: refutability at degree d implies refutability at d+1.
    Embed by keeping the same certificates (degree d ≤ d+1). -/
theorem sos_monotone (F : Type*) [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (n : Nat) (clauses : List (List Int)) (d : Nat)
    (h : SoSRefutable F n clauses d) :
    SoSRefutable F n clauses (d + 1) := by
  obtain ⟨ref⟩ := h
  exact ⟨{
    clause_sos := ref.clause_sos
    clause_sos_bounded := fun i hi =>
      let bsos := ref.clause_sos_bounded i hi
      { summands := bsos.summands
        h_eq := bsos.h_eq
        h_degree := fun q hq => Nat.le_succ_of_le (bsos.h_degree q hq) }
    bool_multipliers := ref.bool_multipliers
    bool_degree_bounded := fun j hj =>
      Nat.le_trans (ref.bool_degree_bounded j hj) (by omega)
    sigma := ref.sigma
    sigma_sos :=
      { summands := ref.sigma_sos.summands
        h_eq := ref.sigma_sos.h_eq
        h_degree := fun q hq => Nat.le_succ_of_le (ref.sigma_sos.h_degree q hq) }
    h_clause_len := ref.h_clause_len
    h_bool_len := ref.h_bool_len
    h_identity := ref.h_identity }⟩

/-- The moment matrix size satisfies: C(n+d, d) ≤ (n+d)^d. -/
theorem moment_matrix_size_bound (n d : Nat) :
    Nat.choose (n + d) d ≤ (n + d) ^ d :=
  Nat.choose_le_pow (n + d) d

end ClassicalConstraints
