/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

ClassicalConstraints/ConcreteEncodings/DirectVariableEncoding.lean

Encoding candidates for the CookEncoding structure.

Candidate 1: Direct variable encoding (identity carrier, identity grade).
Candidate 2: Tseitin transformation on expander-based circuits.
  Definitionally identical encoding to Candidate 1, but with
  circuit-theoretic obstruction profiles and transfer analysis.

STATUS: 0 sorry, 0 Classical.choice.
-/

import ClassicalConstraints.Shared.CookFaithfulness
import ClassicalConstraints.Chain7_Protocol.ProtocolWitnessFamilyLock

namespace ClassicalConstraints.ConcreteEncodings

-- ============================================================
-- Section 1: The direct variable encoding
-- ============================================================

/-- The direct variable encoding: carrier is Nat (representing num_vars
    of a SAT instance at that size), grade is the identity, encode is
    the identity. This is the simplest possible CookEncoding — it does
    nothing to the size parameter.

    This represents the scenario where we index SAT instances by their
    number of variables and the "encoding" is simply recording that count.
    The polynomial bound is linear (degree 1, constant 0). -/
def directVariableEncoding : CookEncoding where
  Carrier := Nat
  grade := fun n => n
  encode := fun n => n
  grade_poly := ⟨1, 0⟩
  h_poly := fun n => by simp [PolyBound.eval]

/-- The grade polynomial evaluates to n. -/
theorem direct_grade_poly_eval (n : Nat) :
    directVariableEncoding.grade_poly.eval n = n := by
  simp [directVariableEncoding, PolyBound.eval]

/-- The encoding is literally the identity. -/
theorem direct_encode_is_id (n : Nat) :
    directVariableEncoding.encode n = n := rfl

/-- The grade of an encoded element equals the input size. -/
theorem direct_grade_of_encode (n : Nat) :
    directVariableEncoding.grade (directVariableEncoding.encode n) = n := rfl

-- ============================================================
-- Section 2: Obstruction profile — equal depth case
-- ============================================================

/-- When both depth functions are the same function f, the obstruction
    profile is trivially faithful: model_depth = sat_depth, so the
    polynomial bounds are the identity.

    This is the case where the encoding preserves depth perfectly —
    no distortion at all. But this is also the VACUOUS case: we have
    not yet connected the depth functions to anything real about SAT. -/
def equalDepthProfile (f : Nat -> Nat) : ObstructionProfile where
  sat_depth := f
  model_depth := f

/-- Equal-depth CookFaithful: trivially faithful because both sides
    are literally the same function. The polynomial bound is constant 1. -/
def equalDepth_cookFaithful (f : Nat -> Nat) :
    CookFaithful directVariableEncoding where
  profile := equalDepthProfile f
  h_lower := ⟨⟨0, 1⟩, fun n => by
    simp [equalDepthProfile, PolyBound.eval]; omega⟩
  h_upper := ⟨⟨0, 1⟩, fun n => by
    simp [equalDepthProfile, PolyBound.eval]; omega⟩

/-- Equal-depth ConsequenceFaithful: h_consequence is trivially
    model_depth n ≤ d → sat_depth n ≤ d, which is f n ≤ d → f n ≤ d. -/
def equalDepth_consequenceFaithful (f : Nat -> Nat) :
    ConsequenceFaithful directVariableEncoding where
  profile := equalDepthProfile f
  h_lower := ⟨⟨0, 1⟩, fun n => by
    simp [equalDepthProfile, PolyBound.eval]; omega⟩
  h_upper := ⟨⟨0, 1⟩, fun n => by
    simp [equalDepthProfile, PolyBound.eval]; omega⟩
  h_consequence := fun _ _ h => h

-- ============================================================
-- Section 3: Obstruction profile — distinct depth case
-- ============================================================

/-- When sat_depth and model_depth differ, the relationship between
    them encodes the encoding's faithfulness. The simplest nontrivial
    case: model_depth = sat_depth (identity relation).

    The INTERESTING case is when they differ, e.g.,
    sat_depth n = n (raw variable count as depth) and
    model_depth n = some function of n related to selfApp behavior.

    For CookFaithful, we only need polynomial bounds between them.
    For ConsequenceFaithful, we additionally need:
      model_depth n ≤ d → sat_depth n ≤ d

    This monotonicity condition requires sat_depth n ≤ model_depth n
    pointwise (taking d = model_depth n). So ConsequenceFaithful
    is strictly stronger than CookFaithful: it forces the SAT depth
    to be bounded by the model depth. -/

/- An obstruction profile where sat_depth ≤ model_depth pointwise
    admits ConsequenceFaithful. -/
def dominatedProfile (sat_depth model_depth : Nat -> Nat)
    (h_dom : forall n, sat_depth n ≤ model_depth n)
    (p_upper : PolyBound)
    (h_upper_bound : forall n, model_depth n ≤ sat_depth n * p_upper.eval n) :
    ConsequenceFaithful directVariableEncoding where
  profile := ⟨sat_depth, model_depth⟩
  h_lower := ⟨⟨0, 1⟩, fun n => by
    simp [PolyBound.eval]
    have := h_dom n
    omega⟩
  h_upper := ⟨p_upper, h_upper_bound⟩
  h_consequence := fun n d hmd => Nat.le_trans (h_dom n) hmd

-- ============================================================
-- Section 4: Where h_consequence gets stuck for general profiles
-- ============================================================

/-- When sat_depth > model_depth at some point, h_consequence fails.
    This is the PRECISE obstruction: if the SAT topology has deeper
    obstructions than the model sees, we cannot derive bounded SAT
    depth from bounded model depth.

    Formally: if sat_depth n₀ > model_depth n₀ for some n₀, then
    h_consequence fails at (n₀, model_depth n₀). -/
theorem consequence_fails_when_sat_exceeds_model
    (sat_depth model_depth : Nat -> Nat)
    (n₀ : Nat)
    (h_exceed : sat_depth n₀ > model_depth n₀) :
    ¬(∀ n d, model_depth n ≤ d → sat_depth n ≤ d) := by
  intro hcon
  have := hcon n₀ (model_depth n₀) (Nat.le_refl _)
  omega

/-- Converse: h_consequence holds if and only if sat_depth ≤ model_depth
    pointwise. This is the EXACT characterization.

    Proof: taking d = model_depth n gives sat_depth n ≤ model_depth n.
    Conversely, if sat_depth n ≤ model_depth n ≤ d, then sat_depth n ≤ d. -/
theorem consequence_iff_dominated (sat_depth model_depth : Nat -> Nat) :
    (∀ n d, model_depth n ≤ d → sat_depth n ≤ d) ↔
    (∀ n, sat_depth n ≤ model_depth n) := by
  constructor
  · intro hcon n
    exact hcon n (model_depth n) (Nat.le_refl _)
  · intro hdom n d hmd
    exact Nat.le_trans (hdom n) hmd

-- ============================================================
-- Section 5: Transfer type analysis for direct encoding
-- ============================================================

/-- For the direct encoding, ProtocolTransfer requires:
    given a BoundedSelector on (family n) with capacity d,
    produce f : M.carrier → M.carrier that is grade-bounded at d
    and agrees with selfApp on grade-≤-d inputs.

    The challenge: BoundedSelector lives in SAT-space (Boolean
    assignments to variables), while f lives in model-space
    (carrier → carrier). The encoding maps SIZE indices, not
    the functions themselves.

    For the direct encoding (identity on Nat), the transfer must:
    1. Take a bounded selector on the family's n-th instance
    2. Convert it into a grade-bounded function on M

    This conversion is the HARD part. The selector factors through
    ≤ d variables. The function f must factor through grade ≤ d.
    But the carrier of M is not Bool^n — it's an abstract type
    with a grade function. The transfer needs a DICTIONARY between
    "SAT assignments restricted to d variables" and "carrier elements
    at grade ≤ d."

    Without such a dictionary, the transfer is not constructible.
    The direct encoding is TOO SIMPLE: it records the size but not
    the structure needed to build the dictionary. -/

/- TransferShape: what a transfer construction would need to provide
    for the direct variable encoding. This is not a proof — it is a
    TYPE-LEVEL SPECIFICATION of the transfer's shape.

    The key missing piece is `dictionary`: a way to convert bounded
    SAT observations into grade-bounded model functions. -/
structure DirectTransferRequirements
    (M : GradedReflModel_Mirror)
    (family : SATFamily) where
  /-- For each size n, a map from bounded-variable Boolean functions
      to grade-bounded model functions. -/
  dictionary : (n : Nat) → (d : Nat) →
    ((family n).Assignment → Bool) →
    (M.carrier → M.carrier)
  /-- The dictionary output is grade-bounded. -/
  h_bounded : ∀ n d (sel : (family n).Assignment → Bool),
    ∀ x, M.grade (dictionary n d sel x) ≤ d
  /-- The dictionary output agrees with selfApp on bounded inputs.
      THIS is the hard condition: it requires that the selector's
      Boolean observation window corresponds to selfApp's behavior
      on grade-bounded inputs. -/
  h_agrees : ∀ n d (sel : (family n).Assignment → Bool),
    ∀ x, M.grade x ≤ d → dictionary n d sel x = M.selfApp x

/-- If DirectTransferRequirements can be constructed, ProtocolTransfer
    follows immediately. -/
def directTransfer_from_requirements
    (M : GradedReflModel_Mirror)
    (family : SATFamily)
    (enc_cf : ConsequenceFaithful directVariableEncoding)
    (req : DirectTransferRequirements M family) :
    ProtocolTransfer M family directVariableEncoding enc_cf where
  transfer := fun n d sel =>
    ⟨req.dictionary n d sel.select,
     req.h_bounded n d sel.select,
     req.h_agrees n d sel.select⟩

-- ============================================================
-- Section 6: Fundamental obstruction analysis
-- ============================================================

/-- The fundamental obstruction for the direct encoding:
    h_agrees requires that for ANY Boolean function sel on assignments,
    the dictionary output agrees with selfApp. But selfApp's behavior
    is SPECIFIC to the model M, while sel can be ANY bounded function.

    The dictionary must somehow "know" that sel is the restriction of
    a correct SAT solver, not an arbitrary Boolean function. This
    knowledge is what the encoding is supposed to provide — but the
    direct encoding (identity on Nat) provides no structural information.

    DIAGNOSIS: The direct encoding fails not because of polynomial bounds
    (those are trivially satisfied) but because it lacks STRUCTURAL
    information connecting SAT topology to model topology. A working
    encoding needs to encode HOW the SAT instance's variable structure
    maps to the model's grade structure, not just the sizes.

    This is the precise sense in which Theorems 1+2 are hard:
    the encoding must carry structural information, not just size bounds. -/

/- The direct encoding trivially satisfies CookFaithful and even
    ConsequenceFaithful (with equal depths), but provides no help
    for ProtocolTransfer. The faithfulness conditions are necessary
    but not sufficient — the encoding must also be STRUCTURALLY
    compatible with the transfer. -/
def direct_encoding_faithfulness_is_easy :
    ConsequenceFaithful directVariableEncoding :=
  equalDepth_consequenceFaithful (fun n => n)


-- ============================================================================
-- Tseitin Encoding (originally TseitinExpanderEncoding.lean)
-- ============================================================================



-- ============================================================
-- Section 1: Abstract circuit representation
-- ============================================================

/-- A circuit gate: AND, OR, NOT, or a variable input. -/
inductive GateType
  | input : GateType
  | and_gate : GateType
  | or_gate : GateType
  | not_gate : GateType

/-- A circuit: a list of gates with wiring (represented as indices). -/
structure Circuit where
  num_inputs : Nat
  gates : List GateType
  wiring : List (List Nat)
  h_wiring_len : wiring.length = gates.length
  output_gate : Nat
  h_output_valid : output_gate < num_inputs + gates.length

/-- Circuit depth: the longest path from any input to the output. -/
def Circuit.depth (c : Circuit) : Nat := c.gates.length

/-- Circuit size: total number of gates. -/
def Circuit.size (c : Circuit) : Nat := c.gates.length

-- ============================================================
-- Section 2: Tseitin encoding parameters
-- ============================================================

/-- Tseitin blowup parameters: clauses per gate and max clause width. -/
structure TseitinParams where
  clauses_per_gate : Nat
  max_clause_width : Nat
  h_clauses : clauses_per_gate ≤ 4
  h_width : max_clause_width ≤ 3

/-- Standard Tseitin parameters. -/
def standardTseitin : TseitinParams where
  clauses_per_gate := 4
  max_clause_width := 3
  h_clauses := Nat.le_refl _
  h_width := Nat.le_refl _

-- ============================================================
-- Section 3: The Tseitin CookEncoding
-- ============================================================

/- The PolyBound type is n^degree + constant. For Tseitin encoding of
   a circuit with n gates, the post-Tseitin variable count is linear in n.
   We use circuit depth as the grade, giving grade(encode n) = n with
   polynomial bound degree 1, constant 0. This is the same carrier as
   the direct encoding but with circuit-theoretic motivation. -/

/-- Tseitin encoding with circuit depth as grade.
    Definitionally identical to directVariableEncoding — both use Nat
    carrier with identity grade. The Tseitin-specific content is in the
    ObstructionProfile (tseitinProfile) and TseitinTransferRequirements,
    not in the CookEncoding carrier/grade. -/
def tseitinEncoding : CookEncoding := directVariableEncoding

-- ============================================================
-- Section 4: Tseitin-specific obstruction profiles
-- ============================================================

/- Tseitin transformation preserves satisfiability exactly: every
   satisfying assignment of the circuit extends uniquely to a satisfying
   assignment of the CNF. Resolution depth on the CNF side is
   polynomially related to circuit depth, bounded by a factor of
   clauses_per_gate per gate. -/

/-- Tseitin profile: model_depth = circuit depth, sat_depth = circuit
    depth * clauses_per_gate. -/
def tseitinProfile (clauses_per_gate : Nat) : ObstructionProfile where
  sat_depth := fun n => n * clauses_per_gate
  model_depth := fun n => n

/-- CookFaithful for Tseitin with the standard profile. -/
def tseitin_cookFaithful (clauses_per_gate : Nat) (hcpg : clauses_per_gate ≥ 1) :
    CookFaithful tseitinEncoding where
  profile := tseitinProfile clauses_per_gate
  h_lower := ⟨⟨0, clauses_per_gate⟩, fun n => by
    simp [tseitinProfile, PolyBound.eval]
    exact Nat.mul_le_mul_left n (Nat.le_add_left clauses_per_gate 1)⟩
  h_upper := ⟨⟨0, 1⟩, fun n => by
    simp [tseitinProfile, PolyBound.eval]
    calc n ≤ n * clauses_per_gate := Nat.le_mul_of_pos_right n hcpg
      _ ≤ n * clauses_per_gate * 2 := Nat.le_mul_of_pos_right _ (by omega)⟩

-- ============================================================
-- Section 5: ConsequenceFaithful for Tseitin
-- ============================================================

/-- ConsequenceFaithful FAILS for the natural Tseitin profile when
    clauses_per_gate >= 2: the multiplicative inflation from cpg
    means sat_depth > model_depth, violating the pointwise domination
    required by h_consequence. -/
theorem tseitin_consequence_fails (clauses_per_gate : Nat)
    (hcpg : clauses_per_gate ≥ 2) :
    ¬(∀ n d, (tseitinProfile clauses_per_gate).model_depth n ≤ d →
              (tseitinProfile clauses_per_gate).sat_depth n ≤ d) := by
  intro hcon
  have h1 := hcon 1 1 (by simp [tseitinProfile])
  simp [tseitinProfile] at h1
  omega

/-- Rescaled Tseitin profile: absorb the cpg factor into model_depth
    so both sides are equal. -/
def tseitinRescaledProfile (clauses_per_gate : Nat) : ObstructionProfile where
  sat_depth := fun n => n * clauses_per_gate
  model_depth := fun n => n * clauses_per_gate

/-- Rescaled Tseitin ConsequenceFaithful: with equal depths,
    h_consequence is trivial. -/
def tseitin_rescaled_consequenceFaithful (clauses_per_gate : Nat) (_hcpg : clauses_per_gate ≥ 1) :
    ConsequenceFaithful tseitinEncoding where
  profile := tseitinRescaledProfile clauses_per_gate
  h_lower := ⟨⟨0, 1⟩, fun n => by
    simp [tseitinRescaledProfile, PolyBound.eval]; omega⟩
  h_upper := ⟨⟨0, 1⟩, fun n => by
    simp [tseitinRescaledProfile, PolyBound.eval]; omega⟩
  h_consequence := fun _ _ h => h

-- ============================================================
-- Section 6: Transfer analysis for Tseitin
-- ============================================================

/- For Tseitin, the transfer has a natural candidate structure:
   1. Tseitin preserves satisfiability EXACTLY
   2. Each gate's CNF contribution is LOCAL (at most 3 variables)
   3. BoundedSelector at capacity d observes d variables
   4. Observing d variables covers roughly d/cpg gates

   A BoundedSelector at capacity d "covers" d/cpg gates. The selector
   can cover all gates on the longest path when d >= cpg * circuit_depth.
   This gives a CANDIDATE for the transfer: map observation of d
   variables to evaluation of the first d/cpg gates. The function is
   grade-bounded at d and agrees with selfApp IF circuit evaluation at
   depth d corresponds to selfApp at grade d.

   The IF is the hard part: it requires the model M's selfApp to match
   circuit evaluation, which is a STRUCTURAL hypothesis about the model.

   COMPARISON:
   - Direct: no structure for the dictionary at all
   - Capability: depth increments by 1, natural but no variable-gate map
   - Tseitin: gate structure provides the dictionary candidate, but
     requires the model to "be" a circuit evaluation model

   CONCLUSION: Tseitin is the strongest candidate for transfer because
   of its gate-by-gate decomposition, but the transfer still requires
   connecting circuit structure to model structure. -/

/-- What Tseitin-specific transfer would need. -/
structure TseitinTransferRequirements
    (M : GradedReflModel_Mirror)
    (family : SATFamily)
    (clauses_per_gate : Nat) where
  /-- Map from gate evaluation at depth k to model function at grade k. -/
  gate_to_model : (n : Nat) → (gate_depth : Nat) →
    (M.carrier → M.carrier)
  /-- Gate evaluation is grade-bounded. -/
  h_gate_bounded : ∀ n k x,
    M.grade (gate_to_model n k x) ≤ k * clauses_per_gate
  /-- Gate evaluation at full depth agrees with selfApp.
      This is the HARD hypothesis. -/
  h_full_agrees : ∀ n x,
    M.grade x ≤ n * clauses_per_gate →
    gate_to_model n n x = M.selfApp x

-- ============================================================
-- Section 7: Summary of the three candidates
-- ============================================================

/-- All three encodings achieve ConsequenceFaithful easily (with
    appropriate profile choices). The difficulty concentrates in
    ProtocolTransfer. This definition witnesses the Tseitin case. -/
def all_candidates_achieve_consequence_faithful :
    ConsequenceFaithful tseitinEncoding :=
  tseitin_rescaled_consequenceFaithful 4 (by omega)


end ClassicalConstraints.ConcreteEncodings
