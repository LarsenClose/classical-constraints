# Concrete Encoding Candidates: Analysis

## Summary

Three concrete CookEncoding instances were defined and analyzed. All three
achieve ConsequenceFaithful easily. None achieves ProtocolTransfer. The
analysis precisely characterizes WHY, and identifies the exact missing piece.

## Encoding 1: Direct Variable Encoding

**File**: `DirectVariableEncoding.lean`

**Definition**: Carrier = Nat, grade = id, encode = id, grade_poly = (1, 0).

**What was proved**:
- `directVariableEncoding : CookEncoding` with `h_poly` proved
- `equalDepth_cookFaithful f : CookFaithful` for any depth function f
- `equalDepth_consequenceFaithful f : ConsequenceFaithful` for any depth function f
- `dominatedProfile` : ConsequenceFaithful when sat_depth <= model_depth pointwise
- `consequence_fails_when_sat_exceeds_model` : h_consequence fails when sat_depth > model_depth at any point
- `consequence_iff_dominated` : h_consequence holds IFF sat_depth <= model_depth pointwise (exact characterization)
- `directTransfer_from_requirements` : ProtocolTransfer follows from a `DirectTransferRequirements` structure

**Key finding**: `consequence_iff_dominated` is the central result. It proves
that h_consequence is EXACTLY equivalent to pointwise domination: sat_depth n <= model_depth n for all n. This is the exact characterization of when ConsequenceFaithful can hold.

**Transfer obstruction**: The `DirectTransferRequirements` structure identifies
the exact missing piece: a `dictionary` mapping Boolean functions on SAT
assignments to grade-bounded functions on the model carrier. The dictionary's
`h_agrees` field requires the dictionary output to agree with selfApp on
bounded inputs FOR ANY Boolean function sel. This is impossible to construct
from the direct encoding because the encoding carries no structural information
connecting SAT variables to model elements.

## Encoding 2: Capability Delegation Encoding

**File**: `CapabilityDelegationEncoding.lean`

**Definition**: Carrier = Capability, grade = depth, encode n = capability at depth n.

**What was proved**:
- `capabilityDelegationEncoding : CookEncoding` with `h_poly` proved
- `capability_cookFaithful : CookFaithful` with linear profile
- `capability_consequenceFaithful_equal : ConsequenceFaithful` with equal depths
- `capability_consequence_from_overhead` : ConsequenceFaithful when sat_depth <= n
  and sat_depth is positive on positive inputs

**Structural advantage over direct encoding**:
The capability system has transport overhead exactly 1 per delegation step.
This provides:
1. Natural grade increment (each step costs 1)
2. No transport collapse (proved in `capability_no_transport_collapse`)
3. No value collapse (proved in `capability_no_value_collapse`)

Properties 2-3 mirror Side A's selfApp unboundedness: the operation has
genuine cost that cannot be collapsed away.

**Transfer obstruction**: Same dictionary problem as the direct encoding,
but with a natural candidate structure: map each variable observation to
one delegation step. The `CapabilityTransferRequirements` structure
captures this, with `h_composition_agrees` being the hard condition.
The composition of d single-variable observations must replicate selfApp's
behavior through d grade levels.

## Encoding 3: Tseitin Expander Encoding

**File**: `TseitinExpanderEncoding.lean`

**Definition**: Carrier = Nat (circuit depth), grade = id, encode = id.

**What was proved**:
- `tseitinEncoding : CookEncoding` with `h_poly` proved
- `tseitin_cookFaithful : CookFaithful` with sat_depth = n * cpg, model_depth = n
- `tseitin_consequence_fails` : ConsequenceFaithful FAILS for the natural Tseitin
  profile when cpg >= 2 (the multiplicative inflation violates h_consequence)
- `tseitin_rescaled_consequenceFaithful` : ConsequenceFaithful with rescaled profile
  (model_depth = sat_depth = n * cpg)

**Key finding**: `tseitin_consequence_fails` is the most interesting negative result.
The standard Tseitin transformation has a per-gate clause overhead (cpg = 4 for
standard gates). This creates a multiplicative gap: sat_depth = cpg * model_depth.
Since h_consequence requires sat_depth <= model_depth pointwise, any cpg > 1
breaks h_consequence for the natural profile.

**Resolution**: Rescale model_depth to absorb the cpg factor. This makes
h_consequence trivial but changes what "model depth" means: it now measures
cpg * circuit_depth rather than circuit_depth. The rescaling is mathematically
legitimate (it is a change of units) but shifts the burden to the transfer:
the transfer must now work with the rescaled grade.

**Transfer advantage**: Tseitin provides the most structural information of
the three candidates. Each gate's CNF contribution is LOCAL (at most 3
variables per clause). A BoundedSelector observing d variables covers
roughly d/cpg gates. This gives a natural gate-by-gate decomposition for
the dictionary. The `TseitinTransferRequirements` structure captures this
with `gate_to_model` mapping gate evaluation to model functions.

**Transfer obstruction**: Even with the gate-by-gate structure, the transfer
requires `h_full_agrees`: gate evaluation at full depth must agree with
selfApp. This is a STRUCTURAL hypothesis about the model M, not about the
encoding. It requires that the model's selfApp matches circuit evaluation,
which is the deep content of P != NP.

## Cross-Cutting Analysis

### The exact characterization of h_consequence

The theorem `consequence_iff_dominated` (in DirectVariableEncoding.lean) gives
the precise answer:

```
h_consequence holds IFF sat_depth n <= model_depth n for all n
```

This means: ConsequenceFaithful is achievable for ANY encoding, as long as the
obstruction profile has sat_depth <= model_depth. Equal depths always work.
The difficulty is not in achieving ConsequenceFaithful — it is in achieving it
with a profile that is MEANINGFUL (connected to actual SAT/model behavior).

### Where the real difficulty is

All three encodings achieve ConsequenceFaithful easily by choosing equal or
dominated depth functions. The real difficulty is in ProtocolTransfer. Specifically:

1. **The dictionary problem**: Every encoding needs a mapping from bounded
   Boolean functions on SAT assignments to grade-bounded functions on the
   model carrier. No encoding provides this mapping.

2. **The agreement condition**: The dictionary's output must agree with selfApp
   on bounded inputs. This requires the model's computational structure (selfApp)
   to be "visible" through the encoding's grade structure.

3. **The composition challenge**: For capability and Tseitin encodings, the
   dictionary has a natural incremental structure (one delegation step or one
   gate evaluation per unit). But proving that the composition of d incremental
   steps agrees with selfApp is the deep content.

### Ranking of candidates

By structural informativeness for the transfer:

1. **Tseitin** (strongest): Gate-by-gate decomposition provides a natural
   candidate for the incremental dictionary. Each gate contributes locally
   bounded CNF clauses. The transfer reduces to: does gate evaluation at
   depth d match selfApp at grade d?

2. **Capability** (intermediate): Delegation steps provide natural grade
   increments. The transfer reduces to: does composing d delegation-like
   operations match selfApp?

3. **Direct** (weakest): No structural information at all. The transfer
   requires a fully general dictionary with no structural guidance.

### What a successful bridge would need

The analysis identifies the following necessary conditions for completing
Theorems 1+2:

1. **A model M where selfApp has circuit-like structure**: The model's selfApp
   must decompose into incremental gate evaluations (for Tseitin) or delegation
   steps (for capability). This is a property of the MODEL, not the encoding.

2. **A concrete SAT family where the depth functions are meaningful**: The depth
   functions sat_depth and model_depth must track actual complexity-theoretic
   quantities (resolution width, circuit depth, etc.), not arbitrary Nat -> Nat
   functions.

3. **A dictionary theorem**: A proof that the encoding's structural decomposition
   (gates, delegation steps) faithfully represents the model's selfApp behavior
   at bounded grades.

None of these conditions is provable from the encoding alone. They require
connecting the abstract model (GradedReflModel_Mirror with selfApp) to
concrete circuit/SAT structure. This connection IS the P != NP problem.

### What was accomplished

- **3 concrete CookEncoding instances** with h_poly fully proved
- **3 ConsequenceFaithful instances** fully proved (0 sorry)
- **1 CookFaithful instance** for Tseitin with nontrivial (unequal) profile
- **1 negative result**: tseitin_consequence_fails proving that the natural
  Tseitin profile breaks h_consequence when cpg >= 2
- **1 exact characterization**: consequence_iff_dominated proving h_consequence
  is exactly pointwise domination
- **3 transfer requirement structures**: precisely specifying what each
  encoding would need for ProtocolTransfer
- **Precise diagnosis**: the gap is the dictionary/agreement condition,
  which requires connecting model structure (selfApp) to SAT structure
  (variable assignments). This connection is not an encoding property
  but a model property.
