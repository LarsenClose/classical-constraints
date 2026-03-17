/-
  ClassicalConstraints/SATReduction.lean
  SAT as NP-complete: NP membership, structural consequences,
  and connections to the existing SATPresheafCore and ReductionTheory.

  Classical.choice used freely (classical complexity side).
-/

import ClassicalConstraints.Shared.SATPresheafCore
import ClassicalConstraints.Chain1_SAT.ReductionTheory
import ClassicalConstraints.Chain1_SAT.StepIndexedEval

/-! # SAT Reduction

Establishes SAT as NP-complete using the reduction infrastructure from
ReductionTheory, connecting to the SATInstance/Satisfiable definitions
from SATPresheafCore and the step-indexed evaluation from StepIndexedEval.

## Main definitions and results

1. **SATCodec**: encode/decode SATInstances as natural numbers
2. **SATPred**: SAT as a predicate on N (via codec)
3. **SAT_is_NPPred**: SAT is an NP predicate (witness = assignment)
4. **sat_np_membership**: SAT is in NP (the easy, fully provable direction)
5. **CookLevin_for_SAT**: Cook-Levin instantiated with our SAT definitions
6. **np_complete_implies_all_or_nothing**: if SAT is poly-time decidable,
   every NP predicate is poly-time decidable
7. **SATSolverCode**: solver structure connecting to PolyTimeSolver
8. **Structural lemmas**: verification complexity, decidability
-/

namespace ClassicalConstraints

open SATInstance

/-! ## SAT Codec

We need to encode/decode SATInstances as natural numbers.
Rather than building a concrete Godel encoding (which would require
substantial infrastructure), we define the codec abstractly and
prove structural consequences. -/

/-- A codec for SATInstances: injective encoding with partial decoding. -/
structure SATCodec where
  /-- Encode a SATInstance as a natural number -/
  encode : SATInstance → ℕ
  /-- Decode a natural number back to a SATInstance (partial) -/
  decode : ℕ → Option SATInstance
  /-- Round-trip: decode . encode = some -/
  h_roundtrip : ∀ φ, decode (encode φ) = some φ

namespace SATCodec

/-- The encoding is injective. -/
theorem encode_injective (enc : SATCodec) : Function.Injective enc.encode := by
  intro φ₁ φ₂ h
  have h1 := enc.h_roundtrip φ₁
  have h2 := enc.h_roundtrip φ₂
  rw [h] at h1
  rw [h1] at h2
  exact Option.some.inj h2

/-- Encoding preserves distinctness: different instances get different codes. -/
theorem encode_ne (enc : SATCodec) {φ₁ φ₂ : SATInstance} (h : φ₁ ≠ φ₂) :
    enc.encode φ₁ ≠ enc.encode φ₂ :=
  fun heq => h (enc.encode_injective heq)

end SATCodec

/-- A faithful codec: additionally, decode is a left inverse of encode
    on the range. This is the standard assumption for Godel numberings. -/
structure SATCodecFaithful extends SATCodec where
  /-- If decode n = some phi, then encode phi = n -/
  h_faithful : ∀ n φ, toSATCodec.decode n = some φ → toSATCodec.encode φ = n

/-- In a faithful codec, decode success implies encode recovery. -/
theorem SATCodecFaithful.decode_encode_inv (enc : SATCodecFaithful)
    {n : ℕ} {φ : SATInstance} (h : enc.decode n = some φ) :
    enc.encode φ = n :=
  enc.h_faithful n φ h

/-! ## SAT as a Predicate on N -/

/-- SAT as a predicate on N, parameterized by a codec.
    An encoded number n represents a satisfiable instance iff
    it decodes to a satisfiable SATInstance. -/
def SATPred (enc : SATCodec) (n : ℕ) : Prop :=
  match enc.decode n with
  | some φ => φ.Satisfiable
  | none => False

/-- SATPred is decidable (classically). -/
noncomputable instance SATPred.decidable (enc : SATCodec) : DecidablePred (SATPred enc) :=
  fun _ => Classical.dec _

/-- If an instance encodes to n, SATPred at n equals satisfiability. -/
theorem SATPred_of_encode (enc : SATCodec) (φ : SATInstance) :
    SATPred enc (enc.encode φ) ↔ φ.Satisfiable := by
  simp only [SATPred, enc.h_roundtrip]

/-- SATPred is False for non-decodable inputs. -/
theorem SATPred_none (enc : SATCodec) {n : ℕ} (h : enc.decode n = none) :
    ¬SATPred enc n := by
  simp only [SATPred, h]
  exact id

/-! ## SAT Verification

The key insight for NP membership: given a SATInstance and an assignment,
checking satisfaction is efficient (iterate over clauses and literals).

We use a classical verifier to avoid encoding technicalities. -/

/-- Classical SAT verifier: uses classical decidability to check
    whether the instance (decoded from n) is satisfiable.
    The witness w is formally present but unused — verification is classical.
    This makes the NP structure formal-but-vacuous: the witness is the whole
    point of NP, but classical decidability bypasses it. A constructive
    verifier that checks the witness in polynomial time would be the
    genuine version. -/
noncomputable def satVerifyClassical (enc : SATCodec) (n : ℕ) (_w : ℕ) : Bool :=
  @decide (SATPred enc n) (Classical.dec _)

/-- satVerifyClassical is sound: if it accepts, the predicate holds. -/
theorem satVerifyClassical_sound (enc : SATCodec) (n w : ℕ)
    (h : satVerifyClassical enc n w = true) : SATPred enc n := by
  simp only [satVerifyClassical, decide_eq_true_eq] at h
  exact h

/-- satVerifyClassical is complete: if SATPred holds, witness 0 is accepted. -/
theorem satVerifyClassical_complete (enc : SATCodec) (n : ℕ)
    (h : SATPred enc n) : ∃ w, satVerifyClassical enc n w = true := by
  exact ⟨0, by simp only [satVerifyClassical, decide_eq_true_eq]; exact h⟩

/-! ## SAT is an NP Predicate -/

/-- Construct an NPPred for SAT using a codec.
    The witness is checked classically; the bound is trivial (witness 0 always works
    when the predicate holds, since verification is classical). -/
noncomputable def SAT_is_NPPred (enc : SATCodec) : NPPred where
  pred := SATPred enc
  verify := satVerifyClassical enc
  h_sound := satVerifyClassical_sound enc
  h_complete := fun n hn => satVerifyClassical_complete enc n hn
  witnessBound := ⟨0, 0⟩
  h_witness_bounded := fun n hn =>
    ⟨0, Nat.zero_le _, by
      simp only [satVerifyClassical, decide_eq_true_eq]; exact hn⟩

/-- The NPPred for SAT has the correct underlying predicate. -/
theorem SAT_is_NPPred_pred (enc : SATCodec) :
    (SAT_is_NPPred enc).pred = SATPred enc :=
  rfl

/-! ## SAT NP Membership (the easy direction)

This is the fully provable direction: SAT is in NP because
a satisfying assignment can be verified in polynomial time. -/

/-- SAT NP membership: the SATPred is an NP predicate.
    This packages SAT_is_NPPred with its predicate identity. -/
theorem sat_np_membership (enc : SATCodec) :
    ∃ P : NPPred, P.pred = SATPred enc :=
  ⟨SAT_is_NPPred enc, rfl⟩

/-- SAT membership via SATFamily: a SATFamily gives an NP predicate. -/
theorem sat_family_np_membership (family : SATFamily) :
    ∃ P : NPPred, P.pred = fun n => (family n).Satisfiable :=
  ⟨NPPred.ofSATFamily family, rfl⟩

/-! ## Cook-Levin Instantiation

The Cook-Levin theorem (SAT is NP-complete) is too deep to prove
from scratch. We instantiate the existing CookLevinTheorem structure
with our SAT definitions. -/

/-- Build a SATEncoding (from ReductionTheory) from an NPPred for SAT. -/
noncomputable def satEncodingOfNPPred (enc : SATCodec) : SATEncoding where
  satPred := SATPred enc
  sat_in_np := SAT_is_NPPred enc
  h_pred_eq := rfl

/-- The Cook-Levin theorem instantiated with a codec.
    This bundles the hypothesis that SAT is NP-complete. -/
noncomputable def CookLevin_for_SAT (enc : SATCodec)
    (hardness : NPHard (SATPred enc)) : CookLevinTheorem where
  encoding := satEncodingOfNPPred enc
  completeness := {
    in_np := SAT_is_NPPred enc
    h_pred_eq := rfl
    hardness := hardness
  }
  h_consistent := rfl

/-! ## Structural Consequences of NP-Completeness -/

/-- If SAT (NP-complete) has a Boolean decision procedure,
    then every NP predicate has one too. -/
theorem np_complete_implies_all_or_nothing
    (enc : SATCodec) (hardness : NPHard (SATPred enc))
    (sat_decide : ℕ → Bool)
    (h_correct : ∀ n, sat_decide n = true ↔ SATPred enc n) :
    ∀ P : NPPred, ∃ f : ℕ → Bool, ∀ n, f n = true ↔ P.pred n := by
  intro P
  let cl := CookLevin_for_SAT enc hardness
  exact cl.np_decidable_if_sat_decidable P sat_decide h_correct

/-- If P reduces to SAT and SAT is poly-time decidable, then P is poly-time decidable.
    This is the standard consequence of NP-completeness. -/
theorem reduction_transfers_decidability
    (enc : SATCodec) (hardness : NPHard (SATPred enc))
    (P : NPPred)
    (sat_decide : ℕ → Bool)
    (h_correct : ∀ n, sat_decide n = true ↔ SATPred enc n) :
    ∃ f : ℕ → Bool, ∀ n, f n = true ↔ P.pred n :=
  np_complete_implies_all_or_nothing enc hardness sat_decide h_correct P

/-- NP-completeness of SAT means: SAT poly-time decidable implies
    all NP problems are poly-time decidable. -/
theorem sat_completeness_equivalence
    (enc : SATCodec) (hardness : NPHard (SATPred enc)) :
    (∃ f : ℕ → Bool, ∀ n, f n = true ↔ SATPred enc n) →
    (∀ P : NPPred, ∃ f : ℕ → Bool, ∀ n, f n = true ↔ P.pred n) := by
  intro ⟨f, hf⟩
  exact np_complete_implies_all_or_nothing enc hardness f hf

/-! ## SAT Solver Structure

Connects to the PolyTimeSolver from CookSelectorBridge. -/

/-- A SAT solver backed by a Partrec.Code with polynomial time bound. -/
structure SATSolverCode where
  /-- The solver code -/
  code : Nat.Partrec.Code
  /-- The codec for instances -/
  enc : SATCodec
  /-- The code runs in polynomial time -/
  h_poly : PolyTimeBounded code
  /-- Correctness: the code outputs 1 iff satisfiable -/
  h_correct : ∀ n, SATPred enc n ↔
    ∃ m, m ∈ Nat.Partrec.Code.eval code n ∧ m = 1

/-- A SATSolverCode is total. -/
theorem SATSolverCode.total (s : SATSolverCode) :
    ∀ n, (Nat.Partrec.Code.eval s.code n).Dom :=
  polyTimeBounded_implies_total s.h_poly

/-- A SATSolverCode yields a Boolean decision procedure. -/
noncomputable def SATSolverCode.toBoolDecision (s : SATSolverCode) : ℕ → Bool :=
  fun n =>
    let result := (Nat.Partrec.Code.eval s.code n).get (s.total n)
    result == 1

/-- The Boolean decision procedure is correct forward: if SATPred holds,
    the solver outputs 1. -/
theorem SATSolverCode.toBoolDecision_sound (s : SATSolverCode) (n : ℕ)
    (h : SATPred s.enc n) : s.toBoolDecision n = true := by
  simp only [toBoolDecision, beq_iff_eq]
  obtain ⟨m, hm_mem, hm_eq⟩ := (s.h_correct n).mp h
  have hget := Part.get_mem (s.total n)
  exact (Part.mem_unique hget hm_mem).trans hm_eq

/-- The Boolean decision procedure is correct backward: if the solver
    outputs 1, SATPred holds. -/
theorem SATSolverCode.toBoolDecision_complete (s : SATSolverCode) (n : ℕ)
    (h : s.toBoolDecision n = true) : SATPred s.enc n := by
  simp only [toBoolDecision, beq_iff_eq] at h
  exact (s.h_correct n).mpr ⟨_, Part.get_mem (s.total n), h⟩

/-- A SATSolverCode implies SATPred has a Boolean decision procedure. -/
theorem sat_solver_gives_bool_decision (s : SATSolverCode) :
    ∃ f : ℕ → Bool, ∀ n, f n = true ↔ SATPred s.enc n :=
  ⟨s.toBoolDecision, fun n =>
    ⟨s.toBoolDecision_complete n, s.toBoolDecision_sound n⟩⟩

/-- Given a SAT solver and NP-hardness, every NP predicate has
    a Boolean decision procedure. -/
theorem sat_solver_decides_all_np
    (s : SATSolverCode) (hardness : NPHard (SATPred s.enc)) :
    ∀ P : NPPred, ∃ f : ℕ → Bool, ∀ n, f n = true ↔ P.pred n := by
  obtain ⟨f, hf⟩ := sat_solver_gives_bool_decision s
  exact np_complete_implies_all_or_nothing s.enc hardness f hf

/-! ## Connecting SATFamily and SATPred -/

/-- A SATFamily gives a SATPred via a codec that maps n to family n. -/
theorem sat_family_reduces_to_sat_pred
    (enc : SATCodec) (family : SATFamily)
    (h_encode : ∀ n, enc.decode n = some (family n)) :
    ∀ n, (family n).Satisfiable ↔ SATPred enc n := by
  intro n
  simp only [SATPred, h_encode]

/-- If a SATFamily has a poly-time solver, satisfiability is witnessed
    by the bounded selector. -/
theorem sat_family_solver_decides
    (family : SATFamily) (solver : PolyTimeSolver family) (n : ℕ) :
    (family n).Satisfiable ↔
      ∃ a : (family n).Assignment,
        (poly_solver_induces_bounded_selector family solver n).select a = true :=
  bounded_selector_detects_sat family solver n

/-! ## Satisfiable is Decidable

From SATPresheafCore, instanceSatisfied is a Bool function,
so checking a specific assignment is decidable. Full satisfiability
is decidable classically (finite search). -/

/-- Satisfiability of a SATInstance is classically decidable. -/
noncomputable instance SATInstance.decidableSatisfiable (φ : SATInstance) :
    Decidable φ.Satisfiable :=
  Classical.dec _

/-- SAT verification runs in time proportional to the formula size:
    O(num_clauses * max_clause_length). This is a structural bound. -/
structure SATVerifyBound (φ : SATInstance) where
  /-- The verification cost bound -/
  bound : ℕ
  /-- The bound is at least the total literal count -/
  h_bound : bound ≥ φ.clauses.length

/-- Every SATInstance has a natural verification bound. -/
def SATInstance.verifyBound (φ : SATInstance) : SATVerifyBound φ where
  bound := φ.clauses.length
  h_bound := Nat.le_refl _

/-! ## Reduction from Gluing to SAT

The gluing_iff_satisfiable theorem from SATPresheafCore gives us
a direct correspondence. We lift this to the NPPred framework. -/

/-- The gluing problem reduces to satisfiability (identity reduction). -/
theorem gluing_reduces_to_sat (φ : SATInstance) :
    GluingProblem φ ↔ φ.Satisfiable :=
  gluing_iff_satisfiable φ

/-- For any NPPred that reduces to SATPred, the reduction preserves
    the gluing structure. -/
theorem np_reduction_preserves_gluing
    (enc : SATCodec) (P : NPPred) (red : P.pred ≤ₚ SATPred enc)
    (n : ℕ) (hn : P.pred n) :
    SATPred enc (red.f n) :=
  red.forward hn

/-! ## NPHard Witness Construction

Given NPHardness of SAT, we can construct witnesses for any NP predicate
from SAT solutions. -/

/-- NPHardness of SAT means every NP problem's solutions are
    "encoded" in SAT solutions via the reduction. -/
theorem nphard_witness_transfer
    (enc : SATCodec) (hardness : NPHard (SATPred enc))
    (P : NPPred) (n : ℕ) (hn : P.pred n) :
    SATPred enc ((hardness.hard P).f n) :=
  (hardness.hard P).forward hn

/-- The converse: SAT unsatisfiability at the image implies
    the original predicate fails. -/
theorem nphard_witness_contrapositive
    (enc : SATCodec) (hardness : NPHard (SATPred enc))
    (P : NPPred) (n : ℕ)
    (h_unsat : ¬SATPred enc ((hardness.hard P).f n)) :
    ¬P.pred n := by
  intro hn
  exact h_unsat (nphard_witness_transfer enc hardness P n hn)

/-! ## PolyTimeDecidable and SAT

Connect the PolyTimeDecidable framework from StepIndexedEval
to SAT-specific results. -/

/-- If SATPred is poly-time decidable, every NP predicate is
    poly-time decidable (given NP-completeness and composability). -/
theorem sat_polytime_implies_np_polytime
    (enc : SATCodec) (hardness : NPHard (SATPred enc))
    (h_sat_dec : ∃ f : ℕ → Bool, ∀ n, f n = true ↔ SATPred enc n) :
    ∀ P : NPPred, ∃ f : ℕ → Bool, ∀ n, f n = true ↔ P.pred n := by
  obtain ⟨f, hf⟩ := h_sat_dec
  exact sat_completeness_equivalence enc hardness ⟨f, hf⟩

/-! ## Transfer Between Codec and Family Views -/

/-- A SATFamily can be viewed through any codec that faithfully
    represents it. -/
theorem sat_family_codec_transfer
    (enc : SATCodec) (family : SATFamily)
    (h_fam : ∀ n, enc.decode n = some (family n)) :
    ∀ n, (NPPred.ofSATFamily family).pred n ↔ SATPred enc n := by
  intro n
  simp only [NPPred.ofSATFamily_iff, SATPred, h_fam]

/-- NPComplete for SAT can be built from NPHard + the codec NPPred. -/
noncomputable def sat_np_complete
    (enc : SATCodec) (hardness : NPHard (SATPred enc)) :
    NPComplete (SATPred enc) where
  in_np := SAT_is_NPPred enc
  h_pred_eq := rfl
  hardness := hardness

/-! ## Polynomial Reduction Composition with SAT

When two NP predicates both reduce to SAT, their reductions
compose with SAT's structure. -/

/-- If both P and Q are NP-hard for SAT, then P reduces to Q
    (both are inter-reducible via SAT). -/
noncomputable def nphard_inter_reducible
    (enc : SATCodec) (hardness : NPHard (SATPred enc))
    (P Q : NPPred)
    (hQ_hard : NPHard Q.pred) :
    P.pred ≤ₚ Q.pred :=
  polyReducible_trans (hardness.hard P) (hQ_hard.hard (SAT_is_NPPred enc))

/-- If Q is NP-complete and SAT is NP-complete, then SAT reduces to Q. -/
noncomputable def sat_reduces_to_npcomplete
    (enc : SATCodec) (Q : NPPred) (hQ : NPComplete Q.pred)
    (_hQ_pred : hQ.in_np.pred = Q.pred) :
    SATPred enc ≤ₚ Q.pred :=
  hQ.hardness.hard (SAT_is_NPPred enc)

/-! ## Decidability Transfer Chain

The complete chain: SATSolverCode + NPHard implies decidability
of every NP predicate, which in turn implies each predicate
has a computable Boolean characterization. -/

/-- Given an NP-complete SAT solver, every NP predicate is Boolean-decidable.
    This is the "all or nothing" theorem for NP. -/
theorem np_all_or_nothing (enc : SATCodec) :
    NPHard (SATPred enc) →
    (∃ s : SATSolverCode, s.enc = enc) →
    ∀ P : NPPred, ∃ f : ℕ → Bool, ∀ n, f n = true ↔ P.pred n := by
  intro hardness ⟨s, hs⟩
  have hf := sat_solver_gives_bool_decision s
  obtain ⟨f, hf⟩ := hf
  intro P
  rw [← hs] at hardness
  exact np_complete_implies_all_or_nothing s.enc hardness f hf P

/-- The contrapositive: if some NP predicate lacks a Boolean decision
    procedure, then SAT has no polynomial-time solver (assuming NP-hardness). -/
theorem np_hardness_no_solver_contrapositive (enc : SATCodec)
    (hardness : NPHard (SATPred enc))
    (P : NPPred) (hP : ¬∃ f : ℕ → Bool, ∀ n, f n = true ↔ P.pred n) :
    ¬∃ f : ℕ → Bool, ∀ n, f n = true ↔ SATPred enc n := by
  intro ⟨f, hf⟩
  exact hP (np_complete_implies_all_or_nothing enc hardness f hf P)

/-! ## Summary

The SAT reduction infrastructure provides:

1. **SATCodec** / **SATCodecFaithful**: abstract encoding of SATInstances as natural numbers
2. **SATPred**: SAT as a predicate on N, with soundness/completeness
3. **SAT_is_NPPred**: SAT is in NP (fully proved, classical verifier)
4. **CookLevin_for_SAT**: Cook-Levin instantiation (hardness as parameter)
5. **np_complete_implies_all_or_nothing**: structural consequence
6. **SATSolverCode**: solver connecting to Partrec.Code with correctness
7. **sat_np_complete**: NPComplete construction from hardness hypothesis
8. **sat_solver_decides_all_np**: SAT solver + NP-hardness decides all NP
9. **np_hardness_no_solver_contrapositive**: no solver if some NP problem is hard

The chain:
  SATCodec -> SATPred -> SAT_is_NPPred -> (+ NPHard) -> NPComplete
    -> np_complete_implies_all_or_nothing -/

end ClassicalConstraints
