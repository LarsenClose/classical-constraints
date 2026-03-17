/-
  ClassicalConstraints/Chain5_Algebraic/BridgeVacuity.lean
  AlgebraicTransferHypothesis is uninhabitable in TC models,
  given ANY family where PCRefutable is achievable.

  Unlike Chain 1 where BoundedSelector (the transfer input) is trivially
  constructible for any SAT instance, Chain 5's transfer input is
  PCRefutable — a universally quantified proof that a formula has a
  bounded-degree PC refutation over every field. This is NOT trivially
  constructible for arbitrary families.

  The bridge vacuity therefore has two layers:

  1. CONDITIONAL: For any family where PCRefutable is achievable at
     some (n, d), AlgebraicTransferHypothesis + SelfAppUnbounded → False.
     The transfer produces a grade-bounded function, Side A blocks it.

  2. CONCRETE: The trivially-refutable family (every instance has the
     empty clause) is PCRefutable at degree 0 over any field. So
     AlgebraicTransferHypothesis over this family + SelfAppUnbounded → False.

  The conditional layer shows the transfer hypothesis is uninhabitable
  whenever the family has ANY refutable instance. The concrete layer
  shows such families exist, making the transfer hypothesis genuinely
  uninhabitable (not vacuously so).

  STATUS: 0 sorry, 0 Classical.choice.
-/

import ClassicalConstraints.Chain5_Algebraic.AlgebraicProofLock
import ClassicalConstraints.Chain5_Algebraic.PolynomialCalculusCore

namespace ClassicalConstraints

-- ════════════════════════════════════════════════════════════
-- Section 1: Conditional vacuity — any refutable instance suffices
-- ════════════════════════════════════════════════════════════

/-- AlgebraicTransferHypothesis is uninhabitable when SelfAppUnbounded
    holds AND the family has a PC-refutable instance.

    This is the direct analogue of Chain 1's transfer_hypothesis_uninhabitable.
    The difference: Chain 1's transfer input (BoundedSelector) is always
    inhabited. Chain 5's transfer input (PCRefutable) requires that the
    family actually has a refutable instance.

    Proof: invoke the transfer at (n, d) with the given PCRefutable proof.
    The transfer produces a grade-d-bounded function agreeing with selfApp.
    Side A blocks the existence of any such function. -/
theorem algebraic_transfer_hypothesis_uninhabitable
    (M : GradedReflModel_AlgMirror)
    (hub : SelfAppUnbounded_AlgMirror M)
    (family : SATFamily)
    (df : DegreeFaithful)
    (tr : AlgebraicTransferHypothesis M family df)
    (n d : Nat)
    (h_refutable : ∀ (F : Type) [Field F],
      PCRefutable F (family n).num_vars (family n).clauses d) :
    False := by
  let ⟨f, hbound, hagree⟩ := tr.transfer n d h_refutable
  exact sideA_no_bounded_certificate M hub d ⟨f, hagree, fun x _ => hbound x⟩

-- ════════════════════════════════════════════════════════════
-- Section 2: Trivially refutable family
-- ════════════════════════════════════════════════════════════

/-- The trivially-refutable family: every instance has 0 variables
    and a single empty clause. The empty clause is always false,
    so the formula is unsatisfiable. clausePoly F n [] = 1,
    so a one-step PC derivation (introduce the clause axiom) refutes it. -/
def triviallyRefutableFamily : SATFamily :=
  fun _ => { num_vars := 0, clauses := [[]] }

/-- The trivially-refutable family is PC-refutable at degree 0
    over any field, at every instance size.

    This follows directly from empty_clause_refutable: the empty
    clause encodes as the polynomial 1, which is its own refutation. -/
theorem triviallyRefutableFamily_refutable (n : Nat) :
    ∀ (F : Type) [Field F],
      PCRefutable F (triviallyRefutableFamily n).num_vars
        (triviallyRefutableFamily n).clauses 0 :=
  fun F _ => empty_clause_refutable F 0

-- ════════════════════════════════════════════════════════════
-- Section 3: Concrete vacuity
-- ════════════════════════════════════════════════════════════

/-- AlgebraicTransferHypothesis over the trivially-refutable family
    is uninhabitable when SelfAppUnbounded holds.

    This is the concrete bridge vacuity: no additional hypothesis
    beyond the transfer and SelfAppUnbounded is needed.

    Proof: the trivially-refutable family is PC-refutable at degree 0,
    so we invoke the conditional vacuity theorem. -/
theorem algebraic_transfer_trivial_family_uninhabitable
    (M : GradedReflModel_AlgMirror)
    (hub : SelfAppUnbounded_AlgMirror M)
    (df : DegreeFaithful)
    (tr : AlgebraicTransferHypothesis M triviallyRefutableFamily df) :
    False :=
  algebraic_transfer_hypothesis_uninhabitable M hub
    triviallyRefutableFamily df tr 0 0
    (triviallyRefutableFamily_refutable 0)

-- ════════════════════════════════════════════════════════════
-- Section 4: The lock theorem is vacuously true (for refutable families)
-- ════════════════════════════════════════════════════════════

/-- The lock theorem's hypothesis set is unsatisfiable for any family
    with a refutable instance.

    AlgebraicTransferHypothesis is a Type (structure), not a Prop,
    so we state emptiness as a function to False. -/
theorem algebraic_lock_hypothesis_unsatisfiable
    (M : GradedReflModel_AlgMirror)
    (hub : SelfAppUnbounded_AlgMirror M)
    (family : SATFamily)
    (df : DegreeFaithful)
    (n d : Nat)
    (h_refutable : ∀ (F : Type) [Field F],
      PCRefutable F (family n).num_vars (family n).clauses d) :
    AlgebraicTransferHypothesis M family df → False :=
  fun tr => algebraic_transfer_hypothesis_uninhabitable M hub family df tr n d h_refutable

-- ════════════════════════════════════════════════════════════
-- Section 5: Transfer implies grade-non-increasing (for refutable families)
-- ════════════════════════════════════════════════════════════

/-- AlgebraicTransferHypothesis implies selfApp is grade-non-increasing,
    given a family with refutable instances at every degree.

    For any x, invoke the transfer at d = grade(x) with a refutation
    at that degree. The returned function agrees with selfApp at x and
    has grade output ≤ grade(x). Therefore grade(selfApp(x)) ≤ grade(x).

    This requires refutability at every degree d, not just one. -/
theorem algebraic_transfer_implies_grade_nonincreasing
    (M : GradedReflModel_AlgMirror)
    (family : SATFamily)
    (df : DegreeFaithful)
    (tr : AlgebraicTransferHypothesis M family df)
    (h_refutable_all : ∀ (d : Nat), ∃ n,
      ∀ (F : Type) [Field F],
        PCRefutable F (family n).num_vars (family n).clauses d) :
    ∀ x, M.grade (M.selfApp x) ≤ M.grade x := by
  intro x
  obtain ⟨n, h_ref⟩ := h_refutable_all (M.grade x)
  let ⟨f, hbound, hagree⟩ := tr.transfer n (M.grade x) h_ref
  rw [← hagree x (Nat.le_refl _)]
  exact hbound x

-- ════════════════════════════════════════════════════════════
-- Section 6: The structural gap — why Chain 5 differs from Chain 1
-- ════════════════════════════════════════════════════════════

/-- STRUCTURAL OBSERVATION: Chain 5's transfer hypothesis is NOT
    vacuously uninhabitable for arbitrary families.

    In Chain 1, TransferHypothesis.transfer takes BoundedSelector as input.
    BoundedSelector is trivially constructible (trivialSelector), so the
    transfer can always be invoked, making the hypothesis unconditionally
    uninhabitable with SelfAppUnbounded.

    In Chain 5, AlgebraicTransferHypothesis.transfer takes PCRefutable
    as input — a universally quantified proof that a formula has a
    bounded-degree PC refutation over every field. This is NOT trivially
    constructible: it requires the formula to actually be unsatisfiable
    and to have a low-degree refutation.

    For families of satisfiable formulas, PCRefutable is uninhabited,
    and the transfer can never be invoked. In this case,
    AlgebraicTransferHypothesis is trivially satisfiable (the transfer
    function's domain is empty) and does NOT conflict with SelfAppUnbounded.

    This is a genuine structural difference, not a proof gap:
    - Chain 1 locks ANY family (the bridge condition conflicts with Side A)
    - Chain 5 locks REFUTABLE families (the bridge condition only fires
      when the formula has a low-degree refutation)

    The lock is still meaningful: the intended families (Tseitin, random k-SAT)
    are unsatisfiable and DO have PC refutations (just at high degree).
    The lock says the transfer cannot map those high-degree refutations
    to grade-bounded functions without contradicting Side A. -/
theorem chain5_structural_gap_witness :
    ∃ (family : SATFamily),
      ∀ (M : GradedReflModel_AlgMirror)
        (_hub : SelfAppUnbounded_AlgMirror M)
        (df : DegreeFaithful)
        (_tr : AlgebraicTransferHypothesis M family df),
      False :=
  ⟨triviallyRefutableFamily,
   fun M _hub df _tr =>
     algebraic_transfer_trivial_family_uninhabitable M _hub df _tr⟩

/-! ## Summary

This file proves five results:

1. **algebraic_transfer_hypothesis_uninhabitable**: For any family with a
   PC-refutable instance at (n, d), AlgebraicTransferHypothesis +
   SelfAppUnbounded → False. The conditional bridge vacuity.

2. **triviallyRefutableFamily / triviallyRefutableFamily_refutable**:
   A concrete family that is PC-refutable at degree 0 over any field.
   Built from the empty clause (clausePoly F n [] = 1).

3. **algebraic_transfer_trivial_family_uninhabitable**: The concrete bridge
   vacuity. AlgebraicTransferHypothesis over the trivially-refutable family
   + SelfAppUnbounded → False, with no additional hypotheses.

4. **algebraic_lock_hypothesis_unsatisfiable**: The lock theorem's hypothesis
   set is unsatisfiable for refutable families. Function form of (1).

5. **chain5_structural_gap_witness**: There EXISTS a family for which the
   transfer hypothesis is uninhabitable, demonstrating the uninhabitability
   is not vacuous.

KEY STRUCTURAL OBSERVATION: Chain 5's transfer input (PCRefutable) is NOT
trivially constructible, unlike Chain 1's (BoundedSelector). The bridge
vacuity is conditional on having a refutable instance. This is a genuine
structural difference: Chain 5's transfer hypothesis only constrains models
for families where refutations exist.
-/

end ClassicalConstraints
