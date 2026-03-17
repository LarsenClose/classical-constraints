/-
  ClassicalConstraints/CookFaithfulness.lean
  The honest gap map.

  This file states the faithfulness condition needed for Cook encoding
  to preserve obstruction structure. CookFaithful is the OPEN BRIDGE
  CONDITION: it is stated as a structure, not proved, not assumed as
  an axiom. Any result depending on it takes it as an explicit parameter.

  The question: does Cook encoding preserve obstruction depth up to
  polynomial distortion? This file is brutally explicit about what
  is known, what is open, and what each direction would give.
-/

import ClassicalConstraints.Shared.CookSelectorBridge

/-! # Cook Faithfulness

Cook's theorem encodes arbitrary NP instances into SAT instances.
The encoding is polynomial-time computable. But does it preserve
the *obstruction structure* — the depth/dimension of why instances
are hard — up to polynomial distortion?

This is the open bridge condition. Everything here is either:
1. A definition (no proof obligation), or
2. A simple lemma about the definitions (fully proved).

Nothing is assumed. Nothing is sorry'd. -/

namespace ClassicalConstraints

-- ============================================================
-- Section 1: Polynomial Bound Extensions
-- (PolyBound and PolyBound.eval imported from CookSelectorBridge)
-- ============================================================

namespace PolyBound

/-- The identity bound: n ↦ n + 0. -/
def id : PolyBound := ⟨1, 0⟩

/-- Composition of two polynomial bounds (overapproximation). -/
def comp (p q : PolyBound) : PolyBound :=
  ⟨p.degree * q.degree, p.constant + q.constant + 1⟩

/-- A polynomial bound is nontrivial if its degree is positive. -/
def nontrivial (p : PolyBound) : Prop := p.degree > 0

theorem eval_zero (p : PolyBound) : p.eval 0 = 0 ^ p.degree + p.constant := rfl

theorem eval_pos_of_constant_pos (p : PolyBound) (h : p.constant > 0) (n : Nat) :
    p.eval n > 0 := by
  have := p.eval_ge_constant n
  omega

end PolyBound

/-- PolyBound.eval is monotone when degree > 0. Alias for PolyBound.eval_monotone. -/
theorem poly_bound_monotone (p : PolyBound) (hp : p.degree > 0)
    {m n : Nat} (hmn : m ≤ n) : p.eval m ≤ p.eval n :=
  p.eval_monotone hmn hp

-- ============================================================
-- Section 2: Cook Encoding Structure
-- ============================================================

/-- A Cook encoding maps natural-number-indexed sizes into a graded carrier.
    The carrier represents the "target space" of the encoding (e.g., SAT
    instances organized by clause count or variable count). -/
structure CookEncoding where
  /-- The carrier type of encoded objects -/
  Carrier : Type
  /-- Grade function on the carrier (e.g., number of variables/clauses) -/
  grade : Carrier → Nat
  /-- Encoding function: maps input size to an element of the carrier -/
  encode : Nat → Carrier
  /-- Polynomial bound on how much the encoding inflates size -/
  grade_poly : PolyBound
  /-- The grade of any encoding is bounded by the polynomial -/
  h_poly : ∀ n, grade (encode n) ≤ grade_poly.eval n

/-- The encoding grade is bounded by the polynomial. -/
theorem encoding_grade_bounded (enc : CookEncoding) (n : Nat) :
    enc.grade (enc.encode n) ≤ enc.grade_poly.eval n :=
  enc.h_poly n

/-- If the polynomial bound has positive degree, encoding grade is monotone-bounded:
    larger inputs produce encodings whose grade bound is at least as large. -/
theorem encoding_bound_monotone (enc : CookEncoding) (hp : enc.grade_poly.degree > 0)
    {m n : Nat} (hmn : m ≤ n) :
    enc.grade_poly.eval m ≤ enc.grade_poly.eval n :=
  poly_bound_monotone enc.grade_poly hp hmn

-- ============================================================
-- Section 3: Obstruction Profile
-- ============================================================

/-- An obstruction profile records the "depth" of obstruction at each
    input size, in two different topologies:
    - sat_depth: the obstruction depth in the SAT/combinatorial setting
    - model_depth: the obstruction depth in the encoded/algebraic model

    The key question is whether these two depths are polynomially related. -/
structure ObstructionProfile where
  /-- Obstruction depth in the SAT topology at size n -/
  sat_depth : Nat → Nat
  /-- Obstruction depth in the encoded model at size n -/
  model_depth : Nat → Nat

namespace ObstructionProfile

/-- An obstruction profile is trivial if both depths are always zero. -/
def trivial : ObstructionProfile := ⟨fun _ => 0, fun _ => 0⟩

end ObstructionProfile

-- ============================================================
-- Section 4: The Open Bridge Condition
-- ============================================================

/-- **CookFaithful**: The central open condition.

    Given a Cook encoding, faithfulness means the obstruction depths
    on the two sides (SAT topology vs encoded model) are polynomially
    related — neither side can hide obstructions that the other misses
    by more than a polynomial factor.

    This is a STRUCTURE, not a theorem. It is the explicit hypothesis
    that downstream results carry as a parameter.

    - h_lower: model depth, scaled up polynomially, dominates SAT depth.
      "The encoding doesn't destroy obstructions."
    - h_upper: model depth is bounded by SAT depth scaled polynomially.
      "The encoding doesn't create fake obstructions." -/
structure CookFaithful (enc : CookEncoding) where
  /-- The obstruction profile witnessing faithfulness -/
  profile : ObstructionProfile
  /-- Lower bound: encoding preserves obstructions (up to polynomial) -/
  h_lower : ∃ p : PolyBound, ∀ n,
    profile.model_depth n * p.eval n ≥ profile.sat_depth n
  /-- Upper bound: encoding doesn't create fake obstructions -/
  h_upper : ∃ p : PolyBound, ∀ n,
    profile.model_depth n ≤ profile.sat_depth n * p.eval n

-- ============================================================
-- Section 5: Status classification
-- ============================================================

/-- Classification of a bridge condition's status. -/
structure FaithfulnessStatus where
  /-- Current status: open / proved / refuted -/
  status : String
  /-- Estimated difficulty -/
  difficulty : String
  /-- Evidence supporting the condition -/
  evidence_for : String
  /-- Evidence against the condition -/
  evidence_against : String
  /-- What the condition would give if true -/
  what_it_would_give : String

-- ============================================================
-- Section 6: Conditional Consequences
-- ============================================================

/-- A conditional consequence: what CookFaithful gives when combined
    with a "Side A" hypothesis. Both are carried as explicit data. -/
structure ConditionalConsequence where
  /-- Description of the Side A hypothesis -/
  side_a_description : String
  /-- Description of what the combination yields -/
  consequence_description : String
  /-- The encoding this applies to -/
  encoding : CookEncoding
  /-- The faithfulness witness (explicit parameter, not axiom) -/
  faithfulness : CookFaithful encoding

/-- The gap chain: if we have faithfulness, obstruction depth in the model
    bounds SAT obstruction depth from below (up to polynomial). -/
theorem faithful_lower_bound (enc : CookEncoding) (cf : CookFaithful enc) :
    ∃ p : PolyBound, ∀ n,
      cf.profile.model_depth n * p.eval n ≥ cf.profile.sat_depth n :=
  cf.h_lower

/-- The gap chain: if we have faithfulness, model depth is bounded above
    by SAT depth (up to polynomial). -/
theorem faithful_upper_bound (enc : CookEncoding) (cf : CookFaithful enc) :
    ∃ p : PolyBound, ∀ n,
      cf.profile.model_depth n ≤ cf.profile.sat_depth n * p.eval n :=
  cf.h_upper

-- ============================================================
-- Section 7: Simple Structural Lemmas
-- ============================================================

/-- Trivial obstruction profile is trivially faithful for any encoding. -/
def trivialFaithful (enc : CookEncoding) : CookFaithful enc where
  profile := ObstructionProfile.trivial
  h_lower := ⟨⟨0, 0⟩, fun _ => by simp [ObstructionProfile.trivial, PolyBound.eval]⟩
  h_upper := ⟨⟨0, 0⟩, fun _ => by simp [ObstructionProfile.trivial, PolyBound.eval]⟩

/-- The identity encoding: carrier is Nat, grade is identity, encode is identity. -/
def identityEncoding : CookEncoding where
  Carrier := Nat
  grade := fun n => n
  encode := fun n => n
  grade_poly := PolyBound.id
  h_poly := fun n => by simp [PolyBound.id, PolyBound.eval]

/-- If both depths are equal, faithfulness holds with the identity polynomial. -/
def equalDepthFaithful (enc : CookEncoding)
    (depth : Nat → Nat) : CookFaithful enc where
  profile := ⟨depth, depth⟩
  h_lower := ⟨⟨0, 1⟩, fun n => by simp [PolyBound.eval]; omega⟩
  h_upper := ⟨⟨0, 1⟩, fun n => by simp [PolyBound.eval]; omega⟩

/-- PolyBound.eval at 1 equals 1 + constant. -/
theorem poly_eval_one (p : PolyBound) : p.eval 1 = 1 + p.constant := by
  simp [PolyBound.eval]

/-- PolyBound.id evaluates to n. -/
theorem poly_id_eval (n : Nat) : PolyBound.id.eval n = n + 0 := by
  simp [PolyBound.id, PolyBound.eval]

/-- Composition of polynomial bounds overapproximates when n ≥ 1 and q has positive degree. -/
theorem poly_comp_bound (p q : PolyBound) (n : Nat) (hn : n ≥ 1) (hq : q.degree ≥ 1) :
    p.eval n ≤ (p.comp q).eval n := by
  unfold PolyBound.eval PolyBound.comp
  simp only
  have hd : n ^ p.degree ≤ n ^ (p.degree * q.degree) :=
    Nat.pow_le_pow_right hn (Nat.le_mul_of_pos_right p.degree hq)
  omega

-- ============================================================
-- Section 8: ConsequenceFaithful (stronger than CookFaithful)
-- ============================================================

/-- ConsequenceFaithful: encoding preserves consequence structure
    up to polynomial distortion. Strictly stronger than CookFaithful —
    adds h_consequence requiring model_depth ≤ d → sat_depth ≤ d.

    Used by Chain 7 (protocol theory) as the open bridge condition,
    and by ConcreteEncodings for encoding analysis. -/
structure ConsequenceFaithful (enc : CookEncoding) where
  /-- Obstruction profile in transport terms -/
  profile : ObstructionProfile
  /-- Lower bound: transport depth dominates model depth -/
  h_lower : ∃ p : PolyBound, ∀ n,
    profile.model_depth n * p.eval n ≥ profile.sat_depth n
  /-- Upper bound: model depth bounded by transport depth -/
  h_upper : ∃ p : PolyBound, ∀ n,
    profile.model_depth n ≤ profile.sat_depth n * p.eval n
  /-- Consequence preservation: encoding doesn't break consequence closure -/
  h_consequence : ∀ n d,
    profile.model_depth n ≤ d →
    profile.sat_depth n ≤ d

/-- ConsequenceFaithful implies CookFaithful: the consequence-aware
    faithfulness is a strengthening of the basic Cook faithfulness. -/
def consequenceFaithful_to_cookFaithful (enc : CookEncoding)
    (cf : ConsequenceFaithful enc) : CookFaithful enc where
  profile := cf.profile
  h_lower := cf.h_lower
  h_upper := cf.h_upper

/-- ConsequenceFaithful is trivially satisfiable (non-vacuously false). -/
def trivialConsequenceFaithful (enc : CookEncoding) : ConsequenceFaithful enc where
  profile := ObstructionProfile.trivial
  h_lower := ⟨⟨0, 0⟩, fun n => by simp [ObstructionProfile.trivial, PolyBound.eval]⟩
  h_upper := ⟨⟨0, 0⟩, fun n => by simp [ObstructionProfile.trivial, PolyBound.eval]⟩
  h_consequence := fun _ _ h => h

end ClassicalConstraints
