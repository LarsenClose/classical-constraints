/-
  ClassicalConstraints/AlgebraicSearchBridge.lean
  Bridge between poly-time SAT refutation and bounded-degree
  algebraic certificates.

  A poly-time solver accessing poly(n) variables induces a bounded-degree
  algebraic certificate (via the multilinear polynomial extension of
  any Boolean function). The bridge is stated as a structure because
  the algebraic simulation of Boolean circuits is deep.

  STATUS: 0 sorry. Classical.choice allowed (Side B).
-/

import ClassicalConstraints.Shared.CookSelectorBridge
import ClassicalConstraints.Chain5_Algebraic.PolynomialCalculusCore
import ClassicalConstraints.Chain5_Algebraic.NullstellensatzCore

namespace ClassicalConstraints

open MvPolynomial

-- ================================================================
-- Section 1: Algebraic capacity from a solver
-- ================================================================

/-- An algebraic capacity bound: the number of variables a solver
    accesses translates to the maximum degree of an algebraic
    certificate it can produce.
    Degree = number of variables accessed = time bound. -/
structure AlgebraicCapacity (family : SATFamily) where
  /-- The degree bound as a function of instance size. -/
  degree_bound : Nat → Nat
  /-- The degree bound is polynomial. -/
  h_poly : ∃ p : PolyBound, ∀ n, degree_bound n ≤ p.eval n

/-- From a PolyTimeSolver, extract the algebraic capacity.
    The degree bound equals the time bound (each step accesses at
    most one new variable, contributing degree 1 to the multilinear
    polynomial encoding). -/
def algebraicCapacityFromSolver (family : SATFamily)
    (solver : PolyTimeSolver family) :
    AlgebraicCapacity family where
  degree_bound := fun n => solver.time_bound.eval n
  h_poly := ⟨solver.time_bound, fun _ => le_refl _⟩

-- ================================================================
-- Section 2: Bounded algebraic approximation
-- ================================================================

/-- A bounded algebraic approximation: for each unsatisfiable instance
    in the family, a degree-bounded PC certificate exists. -/
structure BoundedAlgebraicApproximation (F : Type*) [Field F]
    (family : SATFamily) (cap : AlgebraicCapacity family) where
  /-- For each instance size, if the formula is unsatisfiable,
      a PC derivation of bounded degree exists. -/
  has_certificate : ∀ (n : Nat),
    ¬(family n).Satisfiable →
    PCRefutable F (family n).num_vars (family n).clauses (cap.degree_bound n)

/-- Bounded NS approximation (Nullstellensatz version). -/
structure BoundedNSApproximation (F : Type*) [Field F]
    (family : SATFamily) (cap : AlgebraicCapacity family) where
  /-- For each unsatisfiable instance, an NS certificate of bounded degree. -/
  has_ns_certificate : ∀ (n : Nat),
    ¬(family n).Satisfiable →
    NSRefutable F (family n).num_vars (family n).clauses (cap.degree_bound n)

-- ================================================================
-- Section 3: Solver-to-certificate bridge
-- ================================================================

/-- The main bridge hypothesis: a poly-time solver for a SAT family
    induces bounded-degree algebraic certificates.

    Stated as a structure because the translation from bit-access
    patterns to algebraic degree requires formalizing multilinear
    polynomial extensions of Boolean functions (BooleanToMultilinear).

    Justification: any Boolean function of d variables can be written
    as a multilinear polynomial of degree at most d (Fourier expansion). -/
structure SolverToAlgebraicCertificate (F : Type*) [Field F]
    (family : SATFamily) where
  /-- The polynomial time solver. -/
  solver : PolyTimeSolver family
  /-- The algebraic capacity induced. -/
  capacity : AlgebraicCapacity family
  /-- Capacity matches solver time bound. -/
  h_capacity : capacity = algebraicCapacityFromSolver family solver
  /-- The solver induces bounded algebraic certificates. -/
  has_approximation : BoundedAlgebraicApproximation F family capacity

-- ================================================================
-- Section 4: Boolean function to polynomial conversion
-- ================================================================

/-- Any Boolean function of d variables can be expressed as a
    multilinear polynomial of degree at most d.

    f : {0,1}^d -> {0,1} = sum_{S ⊆ [d]} c_S * prod_{i in S} x_i
    (Fourier expansion / multilinear extension). -/
structure BooleanToMultilinear (F : Type*) [Field F] where
  /-- For any d and any Boolean function on d variables,
      a multilinear polynomial of degree at most d exists. -/
  h_degree : ∀ (d : Nat) (f : (Fin d → Bool) → Bool),
    ∃ (p : MvPolynomial (Fin d) F),
      totalDegree p ≤ d ∧
      ∀ (a : Fin d → Bool),
        MvPolynomial.eval (fun i => if a i then (1 : F) else 0) p =
          if f a then 1 else 0

-- ================================================================
-- Section 5: Connection to BoundedSelector
-- ================================================================

/-- The algebraic bridge factors through the selector bridge.
    A bounded selector accessing d variables computes a Boolean function
    of d variables, which by BooleanToMultilinear is a degree-d polynomial. -/
structure AlgebraicSelectorFactoring (F : Type*) [Field F]
    (family : SATFamily) where
  /-- The solver. -/
  solver : PolyTimeSolver family
  /-- Boolean-to-polynomial conversion. -/
  btm : BooleanToMultilinear F
  /-- The selector polynomial at each instance size. -/
  selector_poly : (n : Nat) → MvPolynomial (Fin (family n).num_vars) F
  /-- The selector polynomial has degree at most the time bound. -/
  h_degree : ∀ n, totalDegree (selector_poly n) ≤ solver.time_bound.eval n
  /-- The selector polynomial agrees with the solver on Boolean inputs. -/
  h_agrees : ∀ n (a : (family n).Assignment),
    MvPolynomial.eval (fun i => if a i then (1 : F) else 0) (selector_poly n) =
      if solver.solve n a then 1 else 0

-- ================================================================
-- Section 6: Proofs
-- ================================================================

/-- A Boolean function on 0 variables is a constant, representable
    at degree 0. -/
theorem bool_zero_var_degree_zero (F : Type*) [Field F]
    (f : (Fin 0 → Bool) → Bool) :
    ∃ (p : MvPolynomial (Fin 0) F),
      totalDegree p ≤ 0 ∧
      ∀ (a : Fin 0 → Bool),
        MvPolynomial.eval (fun i => if a i then (1 : F) else 0) p =
          if f a then 1 else 0 := by
  -- There is only one function Fin 0 → Bool (the empty function),
  -- so f is constant (either always true or always false).
  by_cases hf : f (fun i => i.elim0) = true
  · -- f is always true (since there's only one input)
    exact ⟨1, by simp [MvPolynomial.totalDegree_one],
      fun a => by
        have heqa : a = fun i => i.elim0 := funext (fun i => i.elim0)
        simp only [heqa, hf, if_true, map_one]⟩
  · -- f is always false
    simp only [Bool.not_eq_true] at hf
    exact ⟨0, by simp [MvPolynomial.totalDegree_zero],
      fun a => by
        have heqa : a = fun i => i.elim0 := funext (fun i => i.elim0)
        simp [heqa, hf]⟩

/-- Degree monotonicity: PC-refutability at degree d implies degree d' >= d. -/
theorem pc_refutable_mono (F : Type*) [Field F] (n : Nat)
    (clauses : List (List Int)) (d d' : Nat) (hle : d ≤ d') :
    PCRefutable F n clauses d → PCRefutable F n clauses d' := by
  intro ⟨deriv, hclauses, hdeg⟩
  exact ⟨deriv, hclauses, Nat.le_trans hdeg hle⟩

/-- Algebraic capacity is monotone in the solver's time bound. -/
theorem algebraic_capacity_mono (family : SATFamily)
    (s1 s2 : PolyTimeSolver family)
    (h : ∀ n, s1.time_bound.eval n ≤ s2.time_bound.eval n) :
    ∀ n, (algebraicCapacityFromSolver family s1).degree_bound n ≤
         (algebraicCapacityFromSolver family s2).degree_bound n := by
  intro n
  simp [algebraicCapacityFromSolver]
  exact h n

end ClassicalConstraints
