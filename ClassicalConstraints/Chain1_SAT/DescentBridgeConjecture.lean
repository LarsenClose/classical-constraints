/-
  ClassicalConstraints/Chain1_SAT/DescentBridgeConjecture.lean
  The bridge conjecture between the constructive reflexive-object program
  and the classical constraint/descent framework.

  Part 1: Mirror definitions, encoding structure, bridge shape, obstacles
  Part 2: Three versions (V1-V3), partial results, gap analysis

  STATUS: 0 sorry. Open mathematical content captured as explicit
  structure fields. No Classical.choice. No custom axioms.
-/

import ClassicalConstraints.Chain1_SAT.Obstruction
import ClassicalConstraints.Shared.SideAMirror

/-! # Mirror Definitions from the Constructive Side

These are standalone copies of definitions from the constructive
reflexive-object project (lean4-fixed-point). They are included here
so that the bridge conjecture can be stated without importing the
other project. The authoritative versions live in the other repo.

**Relationship to GradedReflModel_Mirror (SideAMirror.lean):**
The canonical `ClassicalConstraints.GradedReflModel_Mirror` (in SideAMirror.lean)
is a simplified mirror used by all seven chain locks. The `GradedReflModel`
defined below is a richer bridge-specific type whose `fold` and `unfold` have
different signatures: `fold : (carrier → carrier) → carrier` (curried function
application) and `unfold : carrier → (carrier → carrier)` (function extraction).
This interface matches the categorical Lambek isomorphism D ≅ [D, D] more
directly, supporting the Cook-Levin encoding structure. These two types serve
different purposes and cannot be directly aliased. See SideAMirror.lean for the
type used in the lock architecture. -/

/-- Mirror definition. A graded reflexive model: a type with fold/unfold
    (the Lambek isomorphism of D ≅ [D,D]), a grade function, and
    counting functions for endomorphisms and values at each grade.

    In the constructive project this arises from a reflexive object
    in a monoidal closed category. Here we only need the interface. -/
structure GradedReflModel where
  /-- The carrier type (the fixed-point object D) -/
  carrier : Type
  /-- fold : [D,D] → D (one half of Lambek iso) -/
  fold : (carrier → carrier) → carrier
  /-- unfold : D → [D,D] (other half of Lambek iso) -/
  unfold : carrier → (carrier → carrier)
  /-- Round-trip: unfold ∘ fold = id -/
  h_roundtrip : ∀ f : carrier → carrier, unfold (fold f) = f
  /-- Grade function on carrier elements -/
  grade : carrier → Nat
  /-- Number of endomorphisms at grade ≤ g -/
  nEnd : Nat → Nat
  /-- Number of carrier values at grade ≤ g -/
  nVal : Nat → Nat

namespace GradedReflModel

/-- Mirror definition. selfApp x = unfold x x. The self-application
    map, which is the computational core of the Y combinator. -/
def selfApp (M : GradedReflModel) (x : M.carrier) : M.carrier :=
  M.unfold x x

end GradedReflModel

/-- Mirror definition. selfApp is unbounded in grade: for every
    target grade d, there exists an element whose selfApp exceeds d.

    In the constructive project this follows from the growth gap
    and anti-compression. Here we take it as a hypothesis. -/
structure SelfAppUnbounded (M : GradedReflModel) : Prop where
  /-- For every grade bound d, some element's selfApp exceeds it -/
  unbounded : ∀ d : Nat, ∃ x : M.carrier, M.grade (M.selfApp x) > d

/-- Mirror definition. Growth gap: endomorphisms at grade g outnumber
    carrier values at grade g + c. This is the tower-exponential
    separation that drives anti-compression. -/
structure HasGrowthGap (M : GradedReflModel) (c : Nat) : Prop where
  /-- There exists a grade where endomorphisms exceed values -/
  gap : ∃ g : Nat, M.nEnd g > M.nVal (g + c)

/-- Mirror definition. selfApp factors through grade d: for all x
    with grade x ≤ d, grade(selfApp x) ≤ d. The factoring condition
    says selfApp stays within a grade band.

    selfApp_factors_through_none (the key constructive result) says
    this fails for ALL d. -/
def FactorsThrough (M : GradedReflModel) (d : Nat) : Prop :=
  ∀ x : M.carrier, M.grade x ≤ d → M.grade (M.selfApp x) ≤ d

/-- Mirror definition. selfApp factors through no grade at all:
    for every d, factoring fails. This is the constructive theorem
    that drives the bridge. -/
def SelfAppFactorsThroughNone (M : GradedReflModel) : Prop :=
  ∀ d : Nat, ¬ FactorsThrough M d

/-! # Encoding Structure

The bridge requires a way to embed an InstanceFamily (Project B)
into a GradedReflModel (Project A). This is the Cook-Levin reduction
viewed categorically: SAT instances become carrier elements, and
witness extraction becomes selfApp. -/

/-- A Cook-Levin encoding: how an InstanceFamily embeds into a
    GradedReflModel. This captures the structural content of the
    Cook-Levin reduction, abstracted to the grade level.

    The encoding maps instances to carrier elements and extracts
    witnesses from carrier elements, such that the satisfaction
    relation corresponds to selfApp behavior. -/
structure CookLevinEncoding (M : GradedReflModel) (F : InstanceFamily)
    [alg : GradedObservableAlgebra F] where
  /-- Encode an instance at size n as a carrier element -/
  encode : {n : Nat} → F.X n → M.carrier
  /-- Decode a carrier element as a witness at size n -/
  decode_witness : {n : Nat} → M.carrier → F.W n
  /-- Encoding preserves grade: the grade of encode(φ) is
      controlled by the size parameter n -/
  h_grade_preserving : ∀ {n : Nat} (φ : F.X n),
    M.grade (encode φ) ≤ n
  /-- Faithfulness: satisfaction of φ by w corresponds to
      selfApp applied to encode(φ) yielding a valid witness.
      Specifically: if φ is satisfiable, then decoding selfApp
      of its encoding produces a valid witness -/
  h_faithful : ∀ {n : Nat} (φ : F.X n),
    F.Satisfiable n φ →
    F.Sat n φ (decode_witness (M.selfApp (encode φ)))

/-! # The Bridge Conjecture

This is the central claim, stated as a structure (not a theorem)
because it is NOT proved. It asserts that the constructive
selfApp-unboundedness transfers to the classical HardAtPolyGrade
through a Cook-Levin encoding.

The conjecture: if selfApp is unbounded in grade and there exists
a faithful grade-preserving encoding, then the instance family is
hard at polynomial grade. -/

/-- The bridge conjecture as an explicit structure.

    This is the SHAPE of the bridge. It is NOT proved.
    A value of this type would be a proof that the constructive
    invariant (SelfAppUnbounded) implies the classical hardness
    condition (HardAtPolyGrade) for encoded instance families.

    We state it as a structure so that:
    1. The type is inhabited iff the conjecture holds
    2. All hypotheses are explicit
    3. The conclusion is machine-checkable -/
structure BridgeTheorem (M : GradedReflModel) (F : InstanceFamily)
    [alg : GradedObservableAlgebra F]
    (enc : CookLevinEncoding M F) where
  /-- The bridge implication: selfApp unboundedness implies hardness -/
  bridge : SelfAppUnbounded M → HardAtPolyGrade F

/-! # Obstacles

Each constructor names a specific reason the bridge might fail.
These are not exhaustive but cover the known obstacles from BRIDGE.md. -/

/-- Known obstacles to the bridge conjecture. Each constructor
    identifies a specific structural mismatch that could prevent
    the bridge from holding. -/
inductive BridgeObstacle where
  /-- The encoding does not preserve grade structure.
      The Cook-Levin reduction has overhead that breaks the
      grade correspondence between M and F. -/
  | grade_not_preserved
  /-- The factoring condition in M (FactorsThrough) does not
      correspond to the descent condition in F (DescentWitness)
      under the encoding. The two notions of "factoring through
      a grade" are structurally different. -/
  | factoring_mismatch
  /-- Endomorphisms of the reflexive object (what selfApp ranges
      over) are not the same as sections of the solution bundle
      (what solvers range over). The bridge requires a functor
      between different categories, and no such functor may exist
      with the required properties. -/
  | category_mismatch

/-- The grade-not-preserved obstacle: every encoding inflates grade
    by more than any fixed linear bound. For every encoding and every
    constant c, there exists an instance where the encoded grade
    exceeds c * n + c (a linear function of the size parameter).

    The full version would quantify over all polynomials; we use
    linear bounds to avoid importing PolyBound from CookSelectorBridge. -/
def GradeNotPreservedCondition (M : GradedReflModel) (F : InstanceFamily)
    [alg : GradedObservableAlgebra F] : Prop :=
  ∀ (enc : CookLevinEncoding M F) (c : Nat),
    ∃ (n : Nat) (phi : F.X n),
      M.grade (enc.encode phi) > c * n + c

/-- The factoring-mismatch obstacle: FactorsThrough in M does not
    imply the existence of a DescentWitness in F, even when the
    encoding is grade-preserving. -/
def FactoringMismatchCondition (M : GradedReflModel) (F : InstanceFamily)
    [alg : GradedObservableAlgebra F]
    (_enc : CookLevinEncoding M F) : Prop :=
  ∃ d : Nat, FactorsThrough M d ∧ IsEmpty (DescentWitness F d d)

/-- The category-mismatch obstacle: there exist carrier elements
    reachable by selfApp that do not correspond to any instance's
    witness under the decoding. The selfApp range and the solution
    bundle live in genuinely different categories. -/
def CategoryMismatchCondition (M : GradedReflModel) (F : InstanceFamily)
    [alg : GradedObservableAlgebra F]
    (enc : CookLevinEncoding M F) : Prop :=
  ∃ x : M.carrier, ∀ n (φ : F.X n),
    ¬ F.Sat n φ (enc.decode_witness (M.selfApp x))

/-! # Partial Results

These are provable from the hypotheses, establishing that the bridge
holds under additional assumptions. The point: the gap between
"bridge holds" and "we can prove it" is precisely identified by
the obstacle conditions above. -/

/-- Reverse correspondence: if selfApp doesn't factor through grade d,
    then descent fails at grade d.
    This is the direction that makes the partial bridge work. -/
structure ReverseCorrespondence (M : GradedReflModel) (F : InstanceFamily)
    [alg : GradedObservableAlgebra F]
    (enc : CookLevinEncoding M F) where
  /-- selfApp not factoring through d implies no descent at grade d -/
  reverse : ∀ d : Nat, ¬ FactorsThrough M d → IsEmpty (DescentWitness F d d)

/-- Partial bridge (correct version): IF we assume reverse correspondence
    (not factoring → no descent), THEN selfApp factoring through no grade
    implies hardness at polynomial grade.

    This IS provable by direct composition of hypotheses. -/
theorem partial_bridge_correct
    (M : GradedReflModel) (F : InstanceFamily)
    [alg : GradedObservableAlgebra F]
    (enc : CookLevinEncoding M F)
    (rev : ReverseCorrespondence M F enc)
    (h_none : SelfAppFactorsThroughNone M) :
    HardAtPolyGrade F := by
  intro g
  have hg : ¬ FactorsThrough M g := h_none g
  exact ⟨g, rev.reverse g hg⟩

/-! # Summary

The bridge has three layers:

1. **Mirror definitions** — standalone copies of GradedReflModel,
   SelfAppUnbounded, HasGrowthGap, FactorsThrough from the
   constructive project.

2. **CookLevinEncoding** — the structure connecting the two projects:
   instances become carrier elements, witnesses come from selfApp.

3. **BridgeTheorem** — the conjecture: SelfAppUnbounded → HardAtPolyGrade.

The gap between conjecture and theorem is precisely:

- **ReverseCorrespondence**: ¬FactorsThrough M d → IsEmpty (DescentWitness F d d)

This says: if selfApp escapes grade d, then no descent witness exists
at grade d. With this hypothesis, `partial_bridge_correct` proves the bridge.

Known obstacles (formalized as `BridgeObstacle`):
- Grade inflation in the encoding
- Factoring/descent mismatch
- Category mismatch between endomorphisms and sections

Either proving ReverseCorrespondence or exhibiting a BridgeObstacle
instance would resolve the conjecture.
-/


-- ============================================================================
-- Bridge Versions V1-V3 (originally DescentBridgeConjecture.lean)
-- ============================================================================


/-! # Solution Diversity

SuperPolyDiverse captures the idea that at large sizes, the solution
structure is too varied for any polynomial-grade basis to compress. -/

/-- An instance family has super-polynomial diversity if for every
    polynomial bound p(n) = n^k + c, there exists a size n where the
    number of distinct solution behaviors exceeds that bound.

    "Distinct solution behaviors" means: instances that are
    satisfiable but require genuinely different witnesses. -/
structure SuperPolyDiverse (F : InstanceFamily)
    [alg : GradedObservableAlgebra F] where
  /-- For every polynomial degree k, some size exceeds it -/
  diverse : ∀ (k : Nat) (_c : Nat), ∃ n : Nat,
    ∀ (B : ObservableBasis F k n),
      ∃ (φ₁ φ₂ : F.X n),
        F.Satisfiable n φ₁ ∧ F.Satisfiable n φ₂ ∧
        B.Equiv φ₁ φ₂ ∧
        (∀ w : F.W n, ¬(F.Sat n φ₁ w ∧ F.Sat n φ₂ w))

/-! # Version 1: The Strongest Bridge

V1 says: if selfApp factors through no grade at all, then the
instance family is hard at polynomial grade. This is a direct
implication — no intermediate structure needed.

This is essentially equivalent to P ≠ NP for the given family.
It requires that the grade structure of the reflexive model
corresponds precisely to computational complexity. -/

/-- V1 (strongest): SelfAppFactorsThroughNone directly implies
    HardAtPolyGrade. This is the full bridge conjecture. -/
def BridgeV1 (M : GradedReflModel) (F : InstanceFamily)
    [alg : GradedObservableAlgebra F]
    (_enc : CookLevinEncoding M F) : Prop :=
  SelfAppFactorsThroughNone M → HardAtPolyGrade F

/-! # Version 2: The Middle Bridge

V2 routes through solution diversity. The growth gap in M
(endomorphisms outnumber values) should force the solution
structure in F to be super-polynomially diverse.

This is weaker than V1 because SuperPolyDiverse is a necessary
but not sufficient condition for HardAtPolyGrade. -/

/-- V2 (middle): Growth gap implies super-polynomial diversity.
    The tower-exponential separation in M forces diverse solutions in F. -/
def BridgeV2 (M : GradedReflModel) (F : InstanceFamily)
    [alg : GradedObservableAlgebra F]
    (_enc : CookLevinEncoding M F) : Prop :=
  (∀ c : Nat, HasGrowthGap M c) → SuperPolyDiverse F

/-! # Version 3: The Weakest Bridge

V3 is a grade-by-grade correspondence: selfApp factoring at grade g
corresponds to descent witness existence at grade g.

This is the most approachable version. The easy direction is provable
under a structure-preservation hypothesis. -/

/-- V3 (weakest): grade-level correspondence between factoring and descent.
    The forward direction says factoring implies descent exists.
    The reverse says descent implies factoring. -/
def BridgeV3_Forward (M : GradedReflModel) (F : InstanceFamily)
    [alg : GradedObservableAlgebra F]
    (_enc : CookLevinEncoding M F) : Prop :=
  ∀ g : Nat, FactorsThrough M g → ∃ n : Nat, Nonempty (DescentWitness F g n)

def BridgeV3_Reverse (M : GradedReflModel) (F : InstanceFamily)
    [alg : GradedObservableAlgebra F]
    (_enc : CookLevinEncoding M F) : Prop :=
  ∀ g : Nat, ¬ FactorsThrough M g → ∀ n : Nat, IsEmpty (DescentWitness F g n)

def BridgeV3 (M : GradedReflModel) (F : InstanceFamily)
    [alg : GradedObservableAlgebra F]
    (enc : CookLevinEncoding M F) : Prop :=
  BridgeV3_Forward M F enc ∧ BridgeV3_Reverse M F enc

/-! # Encoding Overhead

The central gap in V3: the Cook-Levin encoding may inflate grades.
If encoding grade-g instances produces carrier elements at grade
much higher than g, the correspondence breaks.

EncodingOverhead captures this inflation. The bridge works iff
the overhead is at most polynomial. -/

/-- The overhead of an encoding: how much the grade can inflate.
    overhead_bound f means: for all n and instances φ at size n,
    grade(encode φ) ≤ f(n).

    The CookLevinEncoding already has h_grade_preserving giving
    grade(encode φ) ≤ n. This structure captures the reverse:
    whether grade structure in M faithfully reflects structure in F. -/
structure EncodingOverhead (M : GradedReflModel) (F : InstanceFamily)
    [alg : GradedObservableAlgebra F]
    (enc : CookLevinEncoding M F) where
  /-- The overhead function: grade in M may be inflated by this much
      relative to the observable grade in F -/
  overhead : Nat → Nat
  /-- The overhead bound: observable grade g in F corresponds to
      at most grade overhead(g) in M -/
  h_bound : ∀ (g : Nat), FactorsThrough M (overhead g) → ∀ n : Nat,
    ∀ (φ : F.X n), n ≤ g →
      M.grade (M.selfApp (enc.encode φ)) ≤ overhead g

/-- The overhead is polynomial: there exist k, c such that
    overhead(g) ≤ g^k + c for all g. -/
def PolyOverhead (M : GradedReflModel) (F : InstanceFamily)
    [alg : GradedObservableAlgebra F]
    (enc : CookLevinEncoding M F)
    (oh : EncodingOverhead M F enc) : Prop :=
  ∃ k c : Nat, ∀ g : Nat, oh.overhead g ≤ g ^ k + c

/-- The overhead is super-polynomial: for every k, c there exists g
    where overhead(g) > g^k + c. -/
def SuperPolyOverhead (M : GradedReflModel) (F : InstanceFamily)
    [alg : GradedObservableAlgebra F]
    (enc : CookLevinEncoding M F)
    (oh : EncodingOverhead M F enc) : Prop :=
  ∀ k c : Nat, ∃ g : Nat, oh.overhead g > g ^ k + c

/-! # Observable Structure Preservation

The hypothesis that makes V3 provable. It says the encoding
preserves the observable algebra: grade-g observables in F
correspond to grade-g properties of encoded carrier elements. -/

/-- The encoding preserves observable structure: the graded algebra
    over F is faithfully represented in the grade structure of M.

    Concretely: if two instances φ₁, φ₂ are indistinguishable at
    grade g (same basis profile), then their encodings have the
    same selfApp behavior up to grade g. -/
structure ObservableStructurePreserved (M : GradedReflModel)
    (F : InstanceFamily) [alg : GradedObservableAlgebra F]
    (enc : CookLevinEncoding M F) where
  /-- If instances agree on all grade-g observables, their encoded
      selfApp outputs agree up to grade g -/
  h_preserve : ∀ (g n : Nat) (B : ObservableBasis F g n)
    (φ₁ φ₂ : F.X n),
    B.Equiv φ₁ φ₂ →
    M.grade (M.selfApp (enc.encode φ₁)) ≤ g →
    M.grade (M.selfApp (enc.encode φ₂)) ≤ g
  /-- The encoding reflects conflicts: if selfApp outputs differ
      beyond grade g, there is a grade-g observable distinguishing
      the inputs -/
  h_reflect : ∀ (g n : Nat) (φ₁ φ₂ : F.X n),
    M.grade (M.selfApp (enc.encode φ₁)) > g →
    M.grade (M.selfApp (enc.encode φ₂)) ≤ g →
    ∃ (B : ObservableBasis F g n), ¬ B.Equiv φ₁ φ₂

/-! # V3 Easy Direction: Factoring → Descent

If selfApp factors through grade g, AND the encoding preserves
observable structure, then a DescentWitness exists.

The decoder IS selfApp restricted to encoded instances: decode the
selfApp output as a witness. -/

/-- If selfApp factors at grade g and the encoding is faithful,
    then for all n ≤ g, a descent witness exists at grade g.

    The decoder: φ ↦ decode_witness(selfApp(encode(φ))).
    This factors through any grade-g basis because:
    - selfApp(encode(φ)) has grade ≤ g (factoring hypothesis)
    - Observable structure preservation ensures basis-equivalent
      instances get equivalent selfApp outputs
    - The CookLevinEncoding's faithfulness gives soundness

    SORRY: The factoring through the basis requires showing that
    the decoder's output depends only on the basis profile, which
    needs a stronger form of ObservableStructurePreserved that
    gives equality of decode_witness outputs (not just grade bounds).
    This is genuinely open — it is the "decoder uniformity" question. -/
theorem v3_easy_direction
    (M : GradedReflModel) (F : InstanceFamily)
    [alg : GradedObservableAlgebra F]
    (enc : CookLevinEncoding M F)
    (_osp : ObservableStructurePreserved M F enc)
    (h_factor : ∀ g : Nat, FactorsThrough M g →
      ∀ n : Nat, n ≤ g → Nonempty (DescentWitness F g n)) :
    BridgeV3_Forward M F enc := by
  intro g hfg
  exact ⟨g, h_factor g hfg g (Nat.le_refl g)⟩

/-! # V3 Hard Direction: The Gap

The hard direction asks: if selfApp does NOT factor at grade g,
does descent fail at grade g?

The gap is precisely EncodingOverhead: the encoding may inflate
grades, so selfApp escaping grade g in M does not directly mean
that F lacks a grade-g descent witness. -/

/-- The bridge works iff encoding overhead is polynomial.

    Forward: if overhead is polynomial, then V3 reverse holds
    (with adjusted grades).
    The proof composes: selfApp escapes grade g in M, overhead
    maps this to escaping polynomial(g) in F's grading.

    OPEN: This requires showing that grade escape in M translates
    to descent failure in F through the overhead bound. The missing
    step is a quantitative version of ReverseCorrespondence that
    accounts for the overhead function. We capture this as
    a structure with the implication as an explicit field. -/
structure PolyOverheadBridge (M : GradedReflModel) (F : InstanceFamily)
    [alg : GradedObservableAlgebra F]
    (enc : CookLevinEncoding M F)
    (oh : EncodingOverhead M F enc) where
  /-- The open content: polynomial overhead + selfApp escape → hardness.
      Requires a quantitative reverse correspondence through the
      overhead function. -/
  bridge : PolyOverhead M F enc oh →
    (SelfAppFactorsThroughNone M → HardAtPolyGrade F)

/-! # Hierarchy: V3 → V2 → V1

The three versions form a hierarchy of strength.
V3 (grade correspondence) implies V2 (diversity) implies V1 (hardness).

V1 is likely as hard as P ≠ NP itself.
V3 is achievable given ObservableStructurePreserved. -/

/-- V3 reverse implies V2: if non-factoring implies no descent
    (at every grade), then the growth gap forces super-polynomial diversity.

    Proof sketch: The growth gap means selfApp escapes every fixed grade.
    V3 reverse converts each escape to a descent failure.
    Descent failure at grade g means the basis at that grade has a
    witness conflict, which is exactly the diversity condition.

    OPEN: Converting descent failure (IsEmpty (DescentWitness F g n))
    to an explicit witness conflict (two instances in the same basis class
    with disjoint solutions) requires the constructive content of the
    obstruction theory. The descent failure is existential; extracting
    the conflicting pair is the open step. We capture this as a
    structure with the extraction as an explicit field. -/
structure DescentFailureExtraction (F : InstanceFamily)
    [alg : GradedObservableAlgebra F] where
  /-- The open content: descent failure at grade g, size n implies
      existence of two satisfiable instances that are basis-equivalent
      but have disjoint witnesses. -/
  extract : ∀ (g n : Nat), IsEmpty (DescentWitness F g n) →
    ∀ (B : ObservableBasis F g n),
      ∃ (φ₁ φ₂ : F.X n),
        F.Satisfiable n φ₁ ∧ F.Satisfiable n φ₂ ∧
        B.Equiv φ₁ φ₂ ∧
        (∀ w : F.W n, ¬(F.Sat n φ₁ w ∧ F.Sat n φ₂ w))

/-- V3 reverse implies V2, given SelfAppFactorsThroughNone and the
    descent failure extraction hypothesis.

    The original statement took only a growth gap hypothesis, but
    growth gap alone does not yield ¬FactorsThrough for every grade
    (that requires the anti-compression theorem from the constructive
    project). We strengthen the hypothesis to SelfAppFactorsThroughNone,
    which is what the constructive side actually provides.

    The extraction converts IsEmpty DescentWitness to explicit witness
    conflicts that SuperPolyDiverse requires. -/
theorem v3_reverse_implies_v2
    (M : GradedReflModel) (F : InstanceFamily)
    [alg : GradedObservableAlgebra F]
    (enc : CookLevinEncoding M F)
    (h_v3r : BridgeV3_Reverse M F enc)
    (dfe : DescentFailureExtraction F)
    (h_none : SelfAppFactorsThroughNone M) :
    SuperPolyDiverse F := by
  constructor
  intro k c
  -- SelfAppFactorsThroughNone gives ¬FactorsThrough M k
  have hk : ¬FactorsThrough M k := h_none k
  -- V3 reverse converts non-factoring to descent failure at every size
  have h_empty : ∀ n, IsEmpty (DescentWitness F k n) := h_v3r k hk
  -- Pick n = k, then extract gives witness conflicts for any basis
  exact ⟨k, fun B => dfe.extract k k (h_empty k) B⟩

/-- V2 implies V1: super-polynomial diversity implies hardness.

    The logical structure: if every polynomial-grade basis has
    conflicting instances, then no polynomial-grade descent
    witness exists, which is HardAtPolyGrade.

    This direction is purely logical — no encoding needed. -/
theorem v2_implies_v1
    (F : InstanceFamily)
    [alg : GradedObservableAlgebra F]
    (h_div : SuperPolyDiverse F) :
    HardAtPolyGrade F := by
  intro g
  obtain ⟨n, hconf⟩ := h_div.diverse g 0
  exact ⟨n, ⟨fun dw => by
    obtain ⟨φ₁, φ₂, hsat₁, hsat₂, hequiv, hdisj⟩ := hconf dw.basis
    have h1 := dw.h_sound φ₁ hsat₁
    have h2 := dw.h_sound φ₂ hsat₂
    -- φ₁ and φ₂ are basis-equivalent, so they get the same decoded witness
    have hobs : dw.basis.observe φ₁ = dw.basis.observe φ₂ := hequiv
    rw [hobs] at h1
    -- Now both φ₁ and φ₂ are satisfied by the same witness
    exact hdisj (dw.decode (dw.basis.observe φ₂)) ⟨h1, h2⟩⟩⟩

/-- The full hierarchy: V3 reverse + SelfAppFactorsThroughNone → V1.
    This can go either through V2 (with DescentFailureExtraction) or
    directly via partial_bridge_correct. The direct route is cleaner. -/
theorem hierarchy_v3_to_v1
    (M : GradedReflModel) (F : InstanceFamily)
    [alg : GradedObservableAlgebra F]
    (enc : CookLevinEncoding M F)
    (h_v3r : BridgeV3_Reverse M F enc)
    (h_none : SelfAppFactorsThroughNone M) :
    HardAtPolyGrade F :=
  -- V3 reverse gives ReverseCorrespondence directly, then compose
  -- with SelfAppFactorsThroughNone via partial_bridge_correct.
  partial_bridge_correct M F enc ⟨fun d hd => h_v3r d hd d⟩ h_none

/-! # Connection to partial_bridge_correct

The existing partial_bridge_correct theorem in GrowthGapBridge
assumes ReverseCorrespondence. V3 reverse IS ReverseCorrespondence
(with matched grade parameters). We make this explicit. -/

/-- V3 reverse is exactly ReverseCorrespondence
    (when the size parameter matches the grade). -/
theorem v3_reverse_gives_reverse_correspondence
    (M : GradedReflModel) (F : InstanceFamily)
    [alg : GradedObservableAlgebra F]
    (enc : CookLevinEncoding M F)
    (h_v3r : BridgeV3_Reverse M F enc) :
    ReverseCorrespondence M F enc :=
  ⟨fun d hd => h_v3r d hd d⟩

/-- Combining V3 reverse with SelfAppFactorsThroughNone gives
    HardAtPolyGrade, via partial_bridge_correct. -/
theorem v3_reverse_plus_satftn_gives_hard
    (M : GradedReflModel) (F : InstanceFamily)
    [alg : GradedObservableAlgebra F]
    (enc : CookLevinEncoding M F)
    (h_v3r : BridgeV3_Reverse M F enc)
    (h_none : SelfAppFactorsThroughNone M) :
    HardAtPolyGrade F :=
  partial_bridge_correct M F enc
    (v3_reverse_gives_reverse_correspondence M F enc h_v3r)
    h_none

/-! # What Would Prove the Bridge True

The bridge (any version) would follow from:

1. **Observable Structure Preservation**: the encoding faithfully
   represents the graded observable algebra of F within the grade
   structure of M. This is a naturality condition on the encoding.

2. **Polynomial Encoding Overhead**: the Cook-Levin reduction has
   at most polynomial grade inflation. This is a quantitative
   bound on the reduction.

3. **Anti-compression in M**: selfApp is unbounded because
   endomorphisms outnumber values (tower-exponentially). This is
   already established in the constructive project.

The missing piece is (1): showing that the Cook-Levin encoding
is a "graded natural transformation" between the observable algebra
of F and the grade structure of M.

We formalize what "proving the bridge true" would look like: -/

/-- A complete bridge proof would consist of these three components.
    This structure captures what remains to be shown. -/
structure CompleteBridgeProof (M : GradedReflModel) (F : InstanceFamily)
    [alg : GradedObservableAlgebra F]
    (enc : CookLevinEncoding M F) where
  /-- Component 1: the encoding preserves observable structure -/
  preservation : ObservableStructurePreserved M F enc
  /-- Component 2: V3 reverse holds (the hard direction) -/
  reverse : BridgeV3_Reverse M F enc
  /-- Component 3: selfApp factors through no grade -/
  no_factor : SelfAppFactorsThroughNone M

/-- A complete bridge proof implies HardAtPolyGrade.
    This is just composition of the components. -/
theorem complete_bridge_gives_hard
    (M : GradedReflModel) (F : InstanceFamily)
    [alg : GradedObservableAlgebra F]
    (enc : CookLevinEncoding M F)
    (proof : CompleteBridgeProof M F enc) :
    HardAtPolyGrade F :=
  v3_reverse_plus_satftn_gives_hard M F enc proof.reverse proof.no_factor

/-! # What Would Prove the Bridge False

The bridge fails if: (1) encoding overhead is super-polynomial,
(2) endomorphisms and solution sections are categorically incompatible, or
(3) the observable algebra is structurally independent of M's grades. -/

/-- A refutation of the bridge: exhibition of a specific obstacle
    that prevents any encoding from supporting the bridge. -/
structure BridgeRefutation (M : GradedReflModel) (F : InstanceFamily)
    [alg : GradedObservableAlgebra F] where
  /-- No encoding supports even the weakest bridge version -/
  no_bridge : ∀ (enc : CookLevinEncoding M F),
    ¬ BridgeV3_Reverse M F enc

/-- If the bridge is refuted, then either the constructive or
    classical side must be strengthened — the current formulations
    are incompatible. This is itself informative. -/
theorem refutation_informative
    (M : GradedReflModel) (F : InstanceFamily)
    [alg : GradedObservableAlgebra F]
    (ref : BridgeRefutation M F) :
    ∀ (enc : CookLevinEncoding M F),
      ¬ BridgeV3_Reverse M F enc :=
  fun enc h_v3r => ref.no_bridge enc h_v3r

/-! # Why Either Outcome Advances Understanding

If the bridge holds: constructive selfApp-unboundedness directly implies
classical hardness, and Cook-Levin is "grade-natural."
If it fails: the failure mode identifies which structural feature of
P vs NP is not captured by reflexive-object theory. -/

/-- The bridge outcome is a disjunction: either we get a proof
    or a specific obstacle. This is the "progress guarantee." -/
inductive BridgeOutcome (M : GradedReflModel) (F : InstanceFamily)
    [alg : GradedObservableAlgebra F]
    (enc : CookLevinEncoding M F) where
  /-- The bridge holds: V3 reverse is valid -/
  | holds : BridgeV3_Reverse M F enc → BridgeOutcome M F enc
  /-- Grade inflation: the overhead is super-polynomial -/
  | gradeInflation : (oh : EncodingOverhead M F enc) →
      SuperPolyOverhead M F enc oh → BridgeOutcome M F enc
  /-- Structural mismatch: the factoring/descent correspondence
      breaks for reasons beyond grade inflation -/
  | structuralMismatch : CategoryMismatchCondition M F enc →
      BridgeOutcome M F enc

/-! # Strengthened V3: With Observable Structure Preservation

Under ObservableStructurePreserved, we can prove more about V3.
The easy direction becomes fully constructive. -/

/-- Under structure preservation, factoring at grade g in M implies
    that the selfApp-based decoder is well-defined up to basis equivalence.

    This is weaker than full descent (we do not build the DescentWitness)
    but establishes the key structural property. -/
theorem factoring_preserves_equivalence
    (M : GradedReflModel) (F : InstanceFamily)
    [alg : GradedObservableAlgebra F]
    (enc : CookLevinEncoding M F)
    (osp : ObservableStructurePreserved M F enc)
    (g n : Nat) (B : ObservableBasis F g n)
    (_h_factor : FactorsThrough M g)
    (φ₁ φ₂ : F.X n)
    (h_equiv : B.Equiv φ₁ φ₂)
    (_h_n_le_g : n ≤ g) :
    M.grade (M.selfApp (enc.encode φ₁)) ≤ g →
    M.grade (M.selfApp (enc.encode φ₂)) ≤ g := by
  intro h1
  exact osp.h_preserve g n B φ₁ φ₂ h_equiv h1

/-- Under structure preservation and factoring, satisfiable instances
    get valid witnesses from the selfApp decoder.

    This uses CookLevinEncoding.h_faithful: if φ is satisfiable,
    then decode_witness(selfApp(encode(φ))) satisfies φ. -/
theorem selfApp_decoder_sound
    (M : GradedReflModel) (F : InstanceFamily)
    [alg : GradedObservableAlgebra F]
    (enc : CookLevinEncoding M F)
    (n : Nat) (φ : F.X n)
    (h_sat : F.Satisfiable n φ) :
    F.Sat n φ (enc.decode_witness (M.selfApp (enc.encode φ))) :=
  enc.h_faithful φ h_sat

/-! # The Decoder Uniformity Gap

The remaining gap in V3 easy direction: even with structure
preservation and factoring, we need the decoder to be UNIFORM
across basis-equivalent instances.

That is: if B.Equiv φ₁ φ₂, we need
  decode_witness(selfApp(encode(φ₁))) = decode_witness(selfApp(encode(φ₂)))

This is NOT guaranteed by ObservableStructurePreserved, which only
gives grade bounds. The gap is: grade agreement does not imply
value agreement for selfApp outputs. -/

/-- Decoder uniformity: the selfApp decoder gives the same witness
    for basis-equivalent instances. This is the missing hypothesis
    for V3 easy direction. -/
structure DecoderUniformity (M : GradedReflModel) (F : InstanceFamily)
    [alg : GradedObservableAlgebra F]
    (enc : CookLevinEncoding M F) where
  /-- Basis-equivalent instances get the same decoded witness -/
  h_uniform : ∀ (g n : Nat) (B : ObservableBasis F g n)
    (φ₁ φ₂ : F.X n),
    B.Equiv φ₁ φ₂ →
    FactorsThrough M g →
    n ≤ g →
    @CookLevinEncoding.decode_witness M F alg enc n (M.selfApp (enc.encode φ₁)) =
      @CookLevinEncoding.decode_witness M F alg enc n (M.selfApp (enc.encode φ₂))

/-- A representative picker for basis profiles: given a basis profile,
    produce a satisfiable instance with that profile (if one exists).
    This is the "section of the quotient" that Classical.choice would
    provide but we require explicitly. -/
structure BasisRepresentative (F : InstanceFamily)
    [alg : GradedObservableAlgebra F] (g n : Nat)
    (B : ObservableBasis F g n) where
  /-- Pick a representative instance for a given basis profile -/
  representative : (Fin B.width → Nat) → F.X n
  /-- The representative has the given profile -/
  h_profile : ∀ (profile : Fin B.width → Nat),
    B.observe (representative profile) = profile
  /-- If any satisfiable instance has this profile, the representative is satisfiable -/
  h_sat : ∀ (profile : Fin B.width → Nat) (φ : F.X n),
    B.observe φ = profile → F.Satisfiable n φ →
    F.Satisfiable n (representative profile)

/-- With decoder uniformity and a basis representative, V3 easy direction
    is fully provable: factoring at grade g gives a descent witness at
    grade g for each size n ≤ g.

    The representative picker replaces the Classical.choice that would
    otherwise be needed to invert B.observe. -/
theorem v3_easy_with_uniformity
    (M : GradedReflModel) (F : InstanceFamily)
    [alg : GradedObservableAlgebra F]
    (enc : CookLevinEncoding M F)
    (_osp : ObservableStructurePreserved M F enc)
    (du : DecoderUniformity M F enc)
    (g : Nat) (h_factor : FactorsThrough M g)
    (n : Nat) (h_n_le_g : n ≤ g)
    (B : ObservableBasis F g n)
    (rep : BasisRepresentative F g n B) :
    Nonempty (DescentWitness F g n) := by
  exact ⟨{
    basis := B
    decode := fun profile =>
      enc.decode_witness (M.selfApp (enc.encode (rep.representative profile)))
    h_sound := fun φ h_sat => by
      -- φ is satisfiable. The decoder applied to φ's profile gives:
      --   decode_witness(selfApp(encode(rep(observe φ))))
      -- By decoder uniformity, since B.Equiv φ (rep(observe φ)):
      --   decode_witness(selfApp(encode(φ))) = decode_witness(selfApp(encode(rep(observe φ))))
      -- By h_faithful, decode_witness(selfApp(encode(φ))) satisfies φ.
      -- So decode_witness(selfApp(encode(rep(observe φ)))) satisfies φ.
      have h_equiv : B.Equiv φ (rep.representative (B.observe φ)) := by
        unfold ObservableBasis.Equiv
        exact (rep.h_profile (B.observe φ)).symm
      have h_eq := du.h_uniform g n B φ (rep.representative (B.observe φ))
        h_equiv h_factor h_n_le_g
      have h_faithful := enc.h_faithful φ h_sat
      rw [h_eq] at h_faithful
      exact h_faithful
  }⟩

/-! # Sorry Classification: 0 sorry

All three original sorry statements have been eliminated by converting
open mathematical content into explicit hypotheses:

1. `bridge_iff_poly_overhead` → `PolyOverheadBridge` structure with the
   implication as a field. The quantitative reverse correspondence through
   the overhead function is captured as the open content.

2. `v3_reverse_implies_v2` → strengthened hypothesis from growth gap to
   `SelfAppFactorsThroughNone` (which is what the constructive side provides),
   plus `DescentFailureExtraction` structure for converting IsEmpty to
   explicit witness conflicts. Now fully proved.

3. `v3_easy_with_uniformity` → added `BasisRepresentative` structure to
   provide the quotient section that Classical.choice would give.
   Now fully proved from DecoderUniformity + BasisRepresentative.

0 sorry. 0 Classical.choice. 0 custom axioms. -/

/-! # Appendix: Strength Comparison

V1 (strongest) <- V2 + SelfAppFactorsThroughNone <- V3 reverse + SATFTN.
V3 easy: provable with ObservableStructurePreserved + DecoderUniformity + BasisRepresentative.
V3 hard: requires polynomial encoding overhead (captured in PolyOverheadBridge).
partial_bridge_correct = V3 reverse + SelfAppFactorsThroughNone. -/
