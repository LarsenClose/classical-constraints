# CHAINS.md — Per-Chain Reference

Seven chains, each expressing a verification/search obstruction in a
different classical mathematical domain. Organized by group placement.

---

## Group C: selfApp = id

### Chain 7 — Protocol Theory

**1. Chain identity.**
- **Domain:** Distributed witness systems, protocol composition, consequence closure.
- **Directory:** `ClassicalConstraints/Chain7_Protocol/`
- **Files (9):**
  - `DistributedWitnessCore.lean` — DistributedWitnessSystem, WitnessPath, Aggregation
  - `CapabilityWitnessInstance.lean` — Capability-based witness instance
  - `ConsensusWitnessInstance.lean` — Consensus-based witness instance, WitnessSovereignty
  - `ZKProjectionInstance.lean` — Zero-knowledge projection instance
  - `CoherenceTransportMeasure.lean` — CoherenceMeasure, transport cost tracking
  - `ValueCollapseInstance.lean` — Value collapse instance, consequence_closed_path_realizes
  - `ProtocolWitnessFamilyLock.lean` — Lock theorem, ProtocolTransfer (ConsequenceFaithful moved to Shared/CookFaithfulness.lean)
  - `ProtocolDirectBridge.lean` — ProtocolModelData (4-field), chain7_direct_bridge, ProtocolFragment, ProtocolReduction
  - `BridgeVacuity.lean` — protocol_transfer_uninhabitable, BridgeVacuity for Chain 7

**2. Key structures.**

| Structure | File | Purpose | Source |
|-----------|------|---------|--------|
| `DistributedWitnessSystem` | DistributedWitnessCore.lean | Agents with local certification, transport, projection, and realization | Chain-specific |
| `WitnessPath` | DistributedWitnessCore.lean | Inductive path through transport steps | Chain-specific |
| `Aggregation` | DistributedWitnessCore.lean | Aggregation of local witnesses into global witness | Chain-specific |
| `WitnessSovereignty` | ConsensusWitnessInstance.lean | Certification implies realization + transport closure | Chain-specific |
| `CoherenceMeasure` | CoherenceTransportMeasure.lean | Bounded measure on transport with full-iff-closed characterization | Chain-specific |
| `ConsequenceFaithful` | CookFaithfulness.lean | Encoding preserves consequence structure (extends CookFaithful with h_consequence) | Chain-specific (moot: BridgeVacuity) |
| `ProtocolTransfer` | ProtocolWitnessFamilyLock.lean | BoundedSelector -> grade-bounded function on M | Chain-specific (moot: BridgeVacuity) |
| `ProtocolModelData` | ProtocolDirectBridge.lean | red + grade-non-increasing + idempotent + selfApp_eq_red (4-field) | Chain-specific (moot: selfApp=red + red_grade_le contradicts SelfAppUnbounded) |
| `ProtocolFragment` | ProtocolDirectBridge.lean | Projected subdomain (fixed points of red) with cotrip | Chain-specific |
| `ProtocolReduction` | ProtocolDirectBridge.lean | Grade-non-increasing selfApp-invariant map to projected subdomain | Chain-specific |

**3. Lock theorem.**
```lean
theorem no_bounded_protocol_shortcuts
    (M : GradedReflModel_Mirror)
    (hub : SelfAppUnbounded_Mirror M)
    (family : SATFamily) (enc : CookEncoding)
    (cf : ConsequenceFaithful enc)
    (tr : ProtocolTransfer M family enc cf)
    (solver : PolyTimeSolver family) : False
```
- **File:** `ProtocolWitnessFamilyLock.lean:71-84`
- **Axioms:** propext, sideA_bounded_selector_impossible
- **Bridge path:** Path 1 (lock architecture)
- **Hypotheses:** ConsequenceFaithful, ProtocolTransfer (both MOOT via BridgeVacuity — see below)

**4. Bridge condition.**
- `ConsequenceFaithful enc` — Fields: `profile : ObstructionProfile`, `h_lower`, `h_upper`, `h_consequence` (model_depth <= d implies sat_depth <= d). Strictly stronger than CookFaithful. MOOT: ConsequenceFaithful implies CookFaithful, which feeds TransferHypothesis, which is uninhabitable in TC models (BridgeVacuity.lean). The lock theorem is vacuously true.
- `ProtocolTransfer M family enc cf` — Field: `transfer` mapping BoundedSelector to grade-bounded function agreeing with selfApp. MOOT: same BridgeVacuity argument — transfer uninhabitable when SelfAppUnbounded holds.

**5. Bridge paths.** Both Path 1 and Path 2.

*Path 2 (direct bridge, no custom axioms):*
```lean
theorem chain7_direct_bridge
    (M : GradedReflModel_Mirror)
    (hub : SelfAppUnbounded_Mirror M)
    (pmd : ProtocolModelData M) : False
```
- **File:** `ProtocolDirectBridge.lean:233-237`
- **Axioms:** propext, Quot.sound (no custom axioms)
- **Hypotheses (Path 2):** ProtocolModelData M

*Path 2 bridge condition:*
- `ProtocolModelData M` — Fields: `red` (reduction map), `red_grade_le` (grade-non-increasing), `red_idempotent`, `selfApp_eq_red`.
- **What `red` is:** `DWS.project` — the built-in projection of the DistributedWitnessSystem. Already idempotent and cost-reducing by construction.
- **Concrete facts proved:** `protocol_model_data_grade_nonincreasing`, `protocol_model_data_implies_peqnp`, `protocol_model_data_not_unbounded`. All in ProtocolDirectBridge.lean.

**6. Dependencies.** Imports: SideAMirror.lean (axiom, mirror structures), CookSelectorBridge.lean (SATFamily, PolyTimeSolver, BoundedSelector), CookFaithfulness.lean (CookEncoding, ObstructionProfile). No imports from other chains.

**7. Group placement.** Group C. selfApp = id on the protocol model. Five protocol regimes (capability, consensus, ZK projection, coherence transport, value collapse) each instantiate DistributedWitnessSystem. ConsequenceFaithful includes h_consequence, which is strictly stronger than CookFaithful. ProtocolModelData concretely satisfiable from DWS.project.

---

## Group B: ModelData holds, direct bridge applies

### Chain 5 — Algebraic Proof Complexity

**1. Chain identity.**
- **Domain:** Polynomial Calculus, Nullstellensatz, Sum-of-Squares proof systems. Degree lower bounds.
- **Directory:** `ClassicalConstraints/Chain5_Algebraic/`
- **Files (9):**
  - `PolynomialCalculusCore.lean` — PCRefutable, polynomial proof system definitions
  - `NullstellensatzCore.lean` — NSRefutable, Nullstellensatz proof system
  - `SOSRankCore.lean` — SoSRefutable, Sum-of-Squares proof system
  - `AlgebraicSearchBridge.lean` — Algebraic search bridge structures
  - `DegreeLowerBoundBridge.lean` — AlgebraicDegreeLowerBound, TseitinPCLowerBound, DegreeFaithful
  - `AlgebraicProofLock.lean` — Lock theorems (3 variants), AlgebraicModelData, multilinear bridge
  - `AlgebraicModelConcrete.lean` — capExp, multilinearReduce, multilinearReduce_idempotent
  - `MultilinearReductionConcrete.lean` — Concrete multilinear reduction operations
  - `BridgeVacuity.lean` — BridgeVacuity for Chain 5

**2. Key structures.**

| Structure | File | Purpose | Source |
|-----------|------|---------|--------|
| `AlgebraicDegreeLowerBound` | DegreeLowerBoundBridge.lean | Family with linear degree lower bound for PC refutation | Chain-specific |
| `TseitinPCLowerBound` | DegreeLowerBoundBridge.lean | Tseitin formulas on expanders: PC degree >= c*n | External result (structure) |
| `RandomKSATSoSLowerBound` | DegreeLowerBoundBridge.lean | Random k-SAT: SoS degree >= c*n | External result (structure) |
| `UniformLowDegreeRefuter` | AlgebraicProofLock.lean | Uniform refutation scheme below lower bound | Chain-specific |
| `DegreeFaithful` | DegreeLowerBoundBridge.lean | Encoding preserves algebraic degree up to poly distortion | Chain-specific (moot: BridgeVacuity, Path 1 only) |
| `AlgebraicTransferHypothesis` | AlgebraicProofLock.lean | Bounded-degree PC certificate -> grade-bounded function on M | Chain-specific (moot: BridgeVacuity, Path 1 only) |
| `AlgebraicModelData` | AlgebraicProofLock.lean | red + grade-non-increasing + idempotent + selfApp_eq_red | Chain-specific (moot: selfApp=red + red_grade_le contradicts SelfAppUnbounded) |
| `MultilinearFragment` | AlgebraicProofLock.lean | Subdomain where Lambek cotrip holds | Chain-specific |
| `MultilinearCofinality` | AlgebraicProofLock.lean | Overflow witnesses can be found in multilinear fragment | Chain-specific (moot: ModelData uninhabitable in TC models) |

**3. Lock theorems (3 variants).**

*Standalone (no custom axioms, no transfer):*
```lean
theorem no_uniform_low_degree_refuter
    (family : SATFamily) (lb : AlgebraicDegreeLowerBound)
    (h_family : ...) (refuter : UniformLowDegreeRefuter family lb h_family) :
    False
```
- **File:** `AlgebraicProofLock.lean:116-134`
- **Axioms:** propext, Classical.choice, Quot.sound (no custom axioms)

*Path 1 (via Side A axiom):*
```lean
theorem algebraic_proof_lock_via_transfer
    (M : GradedReflModel_AlgMirror) (hub : SelfAppUnbounded_AlgMirror M)
    (family : SATFamily) (df : DegreeFaithful)
    (tr : AlgebraicTransferHypothesis M family df)
    (n d : Nat) (h_cert : ...) : False
```
- **File:** `AlgebraicProofLock.lean:152-166`
- **Axioms:** propext, Classical.choice, sideA_bounded_selector_impossible, Quot.sound
- **Hypotheses:** DegreeFaithful, AlgebraicTransferHypothesis (both MOOT via BridgeVacuity)

*Path 2 (direct bridge, no custom axioms):*
```lean
theorem chain5_direct_bridge
    (M : GradedReflModel_Mirror) (hub : SelfAppUnbounded_Mirror M)
    (amd : AlgebraicModelData M) : False
```
- **File:** `AlgebraicProofLock.lean:750-754`
- **Axioms:** propext, Quot.sound (no Classical.choice, no custom axioms — strongest axiom profile of any chain result)
- **Hypotheses (Path 2, moot in TC models):** AlgebraicModelData M
- **Mechanism:** AlgebraicModelData provides selfApp = red and red is grade-non-increasing, directly contradicting SelfAppUnbounded via `selfApp_nonincreasing_contradiction`.

*Multilinear variant:*
```lean
theorem chain5_multilinear_bridge
    (M : GradedReflModel_Mirror) (hub : SelfAppUnbounded_Mirror M)
    (frag : MultilinearFragment M) (cof : MultilinearCofinality M frag) :
    False
```
- **File:** `AlgebraicProofLock.lean:683-688`
- **Axioms:** propext, Quot.sound

**4. Bridge condition (Path 2).**
- `AlgebraicModelData M` — Fields: `red` (reduction map), `red_grade_le` (grade-non-increasing), `red_idempotent`, `selfApp_eq_red` (selfApp IS reduction).
- **What `red` is:** `multilinearReduce` — projection modulo Boolean axioms (x_i^2 - x_i = 0). Caps exponents at 1. Grade = totalDegree.
- **Concrete facts proved:** `multilinearReduce_idempotent` (AlgebraicModelConcrete.lean), `capExp_comp_eq` (AlgebraicModelConcrete.lean).
- **What was open (now MOOT):** Providing a GRM whose `selfApp` equals `multilinearReduce`. This requires a fold/unfold roundtrip that multilinear projection cannot support, because it loses structural information (high-degree monomials are collapsed). **MOOT in TC models:** AlgebraicModelData requires selfApp = red (grade-non-increasing), contradicting SelfAppUnbounded. `chain5_direct_bridge` proves M + SelfAppUnbounded + AlgebraicModelData → False.

**5. Bridge path.** Both Path 1 and Path 2. Path 2 is the cleaner route (no custom axioms, propext + Quot.sound only).

**6. Dependencies.** Imports: SideAMirror.lean, CookSelectorBridge.lean, CookFaithfulness.lean. Mathlib (MvPolynomial, CommSemiring). No imports from other chains.

**7. Group placement.** Group B. AlgebraicModelData definable. selfApp = multilinearReduce. red is grade-non-increasing and idempotent. MultilinearFragment has cotrip. MultilinearReduction closes cofinality. GRM instantiation open.

---

### Chain 2 — Proof Complexity

**1. Chain identity.**
- **Domain:** Resolution proof system, communication complexity, lifting theorems, feasible interpolation.
- **Directory:** `ClassicalConstraints/Chain2_ProofComplexity/`
- **Files (10):**
  - `ResolutionWidthCore.lean` — Literal, Clause, CNF, ResolutionRefutation, BooleanCircuit, width-size relationship
  - `CommunicationProtocolBridge.lean` — ProtocolTree, CommProtocol, KWGame, protocol-to-rectangles
  - `KrajicekExtraction.lean` — Krajicek protocol extraction from resolution refutations
  - `LiftingCore.lean` — LiftingGadget, LiftingTheorem, DecisionTree, proto_to_dt, dt_to_proto
  - `FeasibleInterpolationBridge.lean` — SplitCNF, FeasibleInterpolant, feasible interpolation axiom
  - `ProofSearchBridge.lean` — ProofSearchInstance, communication-to-search hardness
  - `ProofComplexityLock.lean` — 10 domain-specific theorems + chain2_complete summary
  - `ProofComplexityPartialLambek.lean` — ProofComplexityModelData, direct bridge
  - `ProofComplexityModelConcrete.lean` — Concrete field verification (dt_to_proto/proto_to_dt)
  - `ResolutionProtocolExtraction.lean` — Width-bounded protocol variant (documentation)

**2. Key structures.**

| Structure | File | Purpose | Source |
|-----------|------|---------|--------|
| `CNF` | ResolutionWidthCore.lean | Conjunctive normal form formula | Chain-specific |
| `ResolutionRefutation` | ResolutionWidthCore.lean | Resolution proof with width and size measures | Chain-specific |
| `CommProtocol` | CommunicationProtocolBridge.lean | Communication protocol between Alice and Bob | Chain-specific |
| `ProtocolTree` | CommunicationProtocolBridge.lean | Binary protocol tree with depth measure | Chain-specific |
| `DecisionTree` | LiftingCore.lean | Boolean decision tree with depth measure | Chain-specific |
| `LiftingTheorem` | LiftingCore.lean | Query-to-communication lifting with gadget | Chain-specific |
| `BooleanCircuit` | ResolutionWidthCore.lean | Boolean circuit with gate count | Chain-specific |
| `InterpolationLowerBound` | FeasibleInterpolationBridge.lean | Circuit lower bound on interpolation function | Chain-specific |
| `ProofComplexityModelData` | ProofComplexityPartialLambek.lean | ModelData for Chain 2 (red = flatten) | Chain-specific (moot: selfApp=red + red_grade_le contradicts SelfAppUnbounded) |

**3. Lock theorem.**

Chain 2's principal result is the direct bridge:
```lean
theorem chain2_direct_bridge
    (M : GradedReflModel_Mirror) (hub : SelfAppUnbounded_Mirror M)
    (pcmd : ProofComplexityModelData M) : False
```
- **File:** `ProofComplexityPartialLambek.lean:293-297`
- **Axioms:** propext, Quot.sound (no custom axioms)
- **Bridge path:** Path 2 (direct bridge)
- **Hypotheses (Path 2, moot in TC models):** ProofComplexityModelData M

Chain 2 has NO Path 1 lock theorem. It is the only chain that is
exclusively Path 2. The `chain2_lock_*` theorems in
ProofComplexityLock.lean are domain-specific stepping stones within
proof complexity (width-to-size transfer, lifting, interpolation,
communication lower bounds) — not the sideA-axiom-dependent lock
architecture pattern used by the other chains.

**4. Bridge condition (Path 2).**
- `ProofComplexityModelData M` — Fields: `red` (reduction map), `red_grade_le` (grade-non-increasing), `red_idempotent`, `selfApp_eq_red`.
- **What `red` is:** `dt_to_proto . proto_to_dt` (flatten). Converts protocol tree to decision tree, re-embeds as protocol tree. Grade = depth.
- **Concrete facts proved:** `proto_to_dt_to_proto_depth_le` (depth non-increasing), `dt_to_proto_roundtrip_idempotent` (idempotent), `proto_to_dt_to_proto_eval` (evaluation-preserving at same-inputs). All in LiftingCore.lean.
- **What was open (now MOOT):** Providing a GRM whose `selfApp` equals flatten. The flatten operation converts bob_sends nodes to alice_sends nodes — structurally different from the original, even though evaluation-equivalent. This information loss means no fold can recover the original protocol. **MOOT in TC models:** `chain2_direct_bridge` proves M + SelfAppUnbounded + ProofComplexityModelData → False.

**5. Bridge path.** Path 2 only. The only chain with exclusively Path 2 (no sideA axiom dependency).

**6. Dependencies.** Imports: SideAMirror.lean (mirror structures only — axiom not used in chain2_direct_bridge), CookSelectorBridge.lean, CookFaithfulness.lean. No imports from other chains.

**7. Group placement.** Group B. ProofComplexityModelData definable. selfApp = flatten (dt_to_proto . proto_to_dt). red is grade-non-increasing and idempotent. GRM instantiation open.

---

### Chain 3 — Descriptive Complexity

**1. Chain identity.**
- **Domain:** Finite model theory, FO+LFP, ESO, pebble games, Immerman-Vardi theorem.
- **Directory:** `ClassicalConstraints/Chain3_Descriptive/`
- **Files (10):**
  - `ESOWitnessCore.lean` — Vocabulary, FiniteStructure, FOFormula, ESOFormula, satVocabulary
  - `FixedPointDefinabilityBridge.lean` — LFPFormula, BoundedLFP, ImmermanVardiTheorem (structure)
  - `PebbleGameObstruction.lean` — PebblePosition, DuplicatorStrategy, KPebbleEquivalent, PebbleFormulaEquivalence (structure)
  - `FOCanonicalForm.lean` — foCanonical, foCanonical_idempotent, foCanonical_depth_le
  - `LocalityBridge.lean` — GaifmanGraph, GaifmanLocality, locality_obstructs_fo_definability
  - `DescriptiveDepthBridge.lean` — Quantifier-rank-to-selector bridges
  - `DescriptiveComplexityLock.lean` — Lock theorem, DefinabilityFaithful, DescriptiveTransferHypothesis
  - `DescriptiveComplexityPartialLambek.lean` — DescriptiveComplexityModelData, direct bridge
  - `DescriptiveComplexityModelConcrete.lean` — Concrete field verification (foCanonical)
  - `BridgeVacuity.lean` — BridgeVacuity for Chain 3

**2. Key structures.**

| Structure | File | Purpose | Source |
|-----------|------|---------|--------|
| `Vocabulary` | ESOWitnessCore.lean | Relational vocabulary (relation names + arities) | Chain-specific |
| `FiniteStructure` | ESOWitnessCore.lean | Finite relational structure over a vocabulary | Chain-specific |
| `FOFormula` | ESOWitnessCore.lean | First-order formula with quantifier depth | Chain-specific |
| `ESOFormula` | ESOWitnessCore.lean | Existential second-order formula | Chain-specific |
| `KPebbleEquivalent` | PebbleGameObstruction.lean | k-pebble equivalence (Duplicator wins) | Chain-specific |
| `ImmermanVardiTheorem` | FixedPointDefinabilityBridge.lean | P = FO+LFP on ordered structures | External result (structure) |
| `PebbleFormulaEquivalence` | PebbleGameObstruction.lean | EF theorem for pebble games | External result (structure) |
| `DefinabilityFaithful` | DescriptiveComplexityLock.lean | Encoding preserves descriptive depth | Chain-specific (moot: BridgeVacuity, Path 1 only) |
| `DescriptiveTransferHypothesis` | DescriptiveComplexityLock.lean | BoundedSelector -> grade-bounded function on M | Chain-specific (moot: BridgeVacuity, Path 1 only) |
| `DescriptiveComplexityModelData` | DescriptiveComplexityPartialLambek.lean | ModelData for Chain 3 (red = foCanonical) | Chain-specific (moot: selfApp=red + red_grade_le contradicts SelfAppUnbounded) |

**3. Lock theorem.**

*Path 1:*
```lean
theorem no_poly_sat_solver_descriptive
    (M : GradedReflModel_Mirror_D3) (hub : SelfAppUnbounded_Mirror_D3 M)
    (family : SATFamily) (enc : CookEncoding)
    (df : DefinabilityFaithful enc)
    (tr : DescriptiveTransferHypothesis M family enc df)
    (solver : PolyTimeSolver family) : False
```
- **File:** `DescriptiveComplexityLock.lean:104-119`
- **Axioms:** propext, sideA_bounded_selector_impossible
- **Hypotheses:** DefinabilityFaithful, DescriptiveTransferHypothesis (both MOOT via BridgeVacuity)

*Path 2 (direct bridge, no custom axioms):*
```lean
theorem chain3_direct_bridge
    (M : GradedReflModel_Mirror) (hub : SelfAppUnbounded_Mirror M)
    (dcmd : DescriptiveComplexityModelData M) : False
```
- **File:** `DescriptiveComplexityPartialLambek.lean:314-318`
- **Axioms:** propext, Quot.sound
- **Hypotheses (Path 2, moot in TC models):** DescriptiveComplexityModelData M

**4. Bridge condition (Path 2).**
- `DescriptiveComplexityModelData M` — Fields: `red`, `red_grade_le`, `red_idempotent`, `selfApp_eq_red`.
- **What `red` is:** `foCanonical` — first-order negation normal form conversion. Grade = quantifier rank.
- **Concrete facts proved:** `foCanonical_depth_le` (quantifier depth non-increasing), `foCanonical_idempotent`, `foCanonical_depth_eq` (depth exactly preserved). All in FOCanonicalForm.lean.
- **What was open (now MOOT):** Providing a GRM whose `selfApp` equals `foCanonical`. NNF conversion collapses syntactically distinct but semantically equivalent formulas (e.g., double negation elimination). The original syntactic form cannot be recovered. **MOOT in TC models:** `chain3_direct_bridge` proves M + SelfAppUnbounded + DescriptiveComplexityModelData → False.

**5. Bridge path.** Both Path 1 and Path 2.

**6. Dependencies.** Imports: SideAMirror.lean, CookSelectorBridge.lean, CookFaithfulness.lean. No imports from other chains.

**7. Group placement.** Group B. DescriptiveComplexityModelData definable. selfApp = foCanonical (NNF). red is grade-non-increasing and idempotent. GRM instantiation open.

---

## Group A / Former Group A: Lock architecture + direct bridges with caveats

### Chain 1 — SAT / Combinatorial

**1. Chain identity.**
- **Domain:** SAT instances, witness conflicts, graded observable algebras, barrier evasion.
- **Directory:** `ClassicalConstraints/Chain1_SAT/`
- **Files (23):**
  - `Observable.lean` — GradedObservableAlgebra
  - `Basis.lean` — ObservableBasis, basis equivalence
  - `Obstruction.lean` — WitnessConflict, no_descent_from_conflict
  - `Descent.lean` — Solver, DescentWitness, HardAtPolyGrade
  - `SATBoundaryLock.lean` — Lock theorem, TransferHypothesis
  - `Barriers.lean` — Barrier evasion (Relativizes_trivial, type_mismatch_tt_vs_obstruction)
  - `SelectionFunction.lean` — Selection function framework
  - `SelectionFunctionUniversality.lean` — Selection function universality
  - `SATReduction.lean` — SAT reductions
  - `ReductionTheory.lean` — Reduction theory
  - `ConcreteInstances.lean` — Concrete SAT instances and hard families
  - `StepIndexedEval.lean` — Step-indexed evaluation
  - `InfoTheory.lean` — Information-theoretic bridge and diagnostics
  - `PolyTimeFromEvaln.lean` — Poly-time from evaluation
  - `DoubleNegationShapes.lean` — Double negation analysis
  - `EMDecomposition.lean` — EM decomposition
  - `QuotientDescentCore.lean` — Quotient descent
  - `MorphismChain.lean` — Morphism chain analysis
  - `SheafObstruction.lean` — Sheaf-theoretic obstruction
  - `PartrecReflexive.lean` — Partial recursive reflexive structures
  - `DescentBridgeConjecture.lean` — Descent bridge conjecture
  - `SATDirectBridge.lean` — SATModelData (2-field), chain1_direct_bridge, grade-non-increasing suffices
  - `BridgeVacuity.lean` — transfer_implies_grade_nonincreasing, transfer_hypothesis_uninhabitable

**2. Key structures.**

| Structure | File | Purpose | Source |
|-----------|------|---------|--------|
| `InstanceFamily` | Basic.lean | Parameterized family of instances with decidable satisfaction | Shared |
| `GradedObservableAlgebra` | Observable.lean | Graded algebra of observables with polynomial range | Chain-specific |
| `ObservableBasis` | Basis.lean | Finite basis for observable algebra at grade g, size n | Chain-specific |
| `WitnessConflict` | Obstruction.lean | Two basis-equivalent instances with disjoint solutions | Chain-specific |
| `TransferHypothesis` | SATBoundaryLock.lean | BoundedSelector -> grade-bounded function on M | Chain-specific (moot: BridgeVacuity) |
| `SATModelData` | SATDirectBridge.lean | grade-non-increasing selfApp (2-field ModelData) | Chain-specific (moot: selfApp_grade_le contradicts SelfAppUnbounded) |

**3. Lock theorem.**
```lean
theorem no_poly_sat_solver
    (M : GradedReflModel_Mirror) (hub : SelfAppUnbounded_Mirror M)
    (family : SATFamily) (enc : CookEncoding) (cf : CookFaithful enc)
    (tr : TransferHypothesis M family enc cf)
    (solver : PolyTimeSolver family) : False
```
- **File:** `SATBoundaryLock.lean:65-80`
- **Axioms:** propext, sideA_bounded_selector_impossible
- **Bridge path:** Path 1 only
- **Hypotheses:** CookFaithful enc, TransferHypothesis M family enc cf (both MOOT via BridgeVacuity)

**4. Bridge condition.**
- `CookFaithful enc` — Fields: `profile : ObstructionProfile`, `h_lower` (encoding preserves obstructions), `h_upper` (no fake obstructions). Defined in CookFaithfulness.lean. MOOT: even if satisfied, downstream TransferHypothesis is uninhabitable in TC models (BridgeVacuity.lean).
- `TransferHypothesis M family enc cf` — Field: `transfer` mapping BoundedSelector to grade-bounded function agreeing with selfApp. MOOT: `transfer_hypothesis_uninhabitable` proves this + SelfAppUnbounded → False.

**5. Bridge paths.** Both Path 1 and Path 2.

*Path 2 (direct bridge, no custom axioms):*
```lean
theorem chain1_direct_bridge
    (M : GradedReflModel_Mirror)
    (hub : SelfAppUnbounded_Mirror M)
    (smd : SATModelData M) : False
```
- **File:** `SATDirectBridge.lean:104-110`
- **Axioms:** propext, Quot.sound (no custom axioms)
- **Hypotheses (Path 2):** SATModelData M

*Path 2 bridge condition:*
- `SATModelData M` — Field: `selfApp_grade_le` (grade-non-increasing selfApp). Minimal 2-field structure: grade-non-increasing suffices; no idempotence needed. Uses `selfApp_nonincreasing_contradiction` with f = selfApp (h_eq is reflexivity).
- **What makes Chain 1 different:** No canonical reduction map distinct from selfApp. In the Cook-Levin GRM, selfApp = witness extraction, which is NOT idempotent. The direct bridge uses selfApp itself as the reduction (trivially h_eq : selfApp x = selfApp x).
- **Connection to TransferHypothesis:** `transferHypothesis_to_SATModelData` proves TransferHypothesis implies SATModelData.

**6. Dependencies.** Imports: SideAMirror.lean (axiom), CookSelectorBridge.lean, CookFaithfulness.lean, Basic.lean. No imports from other chains.

**7. Group placement.** Chain 1 has a direct bridge via SATModelData (2-field, grade-non-increasing selfApp). Structurally weaker than Group B's 4-field ModelData — no idempotent reduction map, no selfApp_eq_red beyond the trivial case. The bridge reduces to whether selfApp is grade-non-increasing.

---

### Chain 4 — Constraint Satisfaction Problems

**1. Chain identity.**
- **Domain:** CSP templates, polymorphism algebras, Bulatov-Zhuk dichotomy.
- **Directory:** `ClassicalConstraints/Chain4_CSP/`
- **Files (8):**
  - `CSPInstanceCore.lean` — CSPDomain, ConstraintLanguage, CSPInstance, satToCSP
  - `PolymorphismCore.lean` — Polymorphism, PolClone, WNU, MajorityOp, majority_is_wnu
  - `TractabilityDichotomy.lean` — BulatovZhukDichotomy, SchaeferDichotomy
  - `WidthFromPolymorphisms.lean` — KLConsistency, HasBoundedWidth, threeSAT_no_bounded_width
  - `CSPSelectorBridge.lean` — PolyTimeCSPSolver, BoundedAlgebraicWitness, solver_induces_witness
  - `CSPAlgebraLock.lean` — Lock theorems, CSPTransferHypothesis, PolymorphismFaithful, CSPRegimeTransfer
  - `CSPDirectBridge.lean` — CSPModelData (4-field), WNUGRMData, chain4_wnu_direct_bridge, multi-sorted obstacle
  - `BridgeVacuity.lean` — BridgeVacuity for Chain 4

**2. Key structures.**

| Structure | File | Purpose | Source |
|-----------|------|---------|--------|
| `CSPDomain` | CSPInstanceCore.lean | Finite domain for CSP variables | Chain-specific |
| `ConstraintLanguage` | CSPInstanceCore.lean | Set of allowed constraint relations | Chain-specific |
| `CSPInstance` | CSPInstanceCore.lean | Concrete CSP instance | Chain-specific |
| `PolyTimeCSPSolver` | CSPSelectorBridge.lean | Poly-time CSP solver with bounded variable access | Chain-specific |
| `BoundedAlgebraicWitness` | CSPSelectorBridge.lean | Bounded witness from solver | Chain-specific |
| `CSPTransferHypothesis` | CSPAlgebraLock.lean | BoundedAlgebraicWitness -> grade-bounded function on M | Chain-specific (moot: BridgeVacuity) |
| `PolymorphismFaithful` | CSPAlgebraLock.lean | Clone-level depth distortion is polynomial | Chain-specific (moot: BridgeVacuity) |
| `CSPRegimeTransfer` | CSPAlgebraLock.lean | Bundle: transfer + faithfulness + hardness | Chain-specific (moot: BridgeVacuity) |
| `CSPModelData` | CSPDirectBridge.lean | red + grade-non-increasing + idempotent + selfApp_eq_red (4-field) | Chain-specific (tractable case only) |
| `WNUGRMData` | CSPDirectBridge.lean | Canonical GRM from WNU polymorphism (carrier = D, grade = 0, selfApp = id) | Chain-specific |

**3. Lock theorems.**
```lean
theorem no_poly_csp_solver_via_transfer
    (M : GradedReflModel_Mirror) (hub : SelfAppUnbounded_Mirror M)
    (dom : CSPDomain) (lang : ConstraintLanguage dom)
    (inst : CSPInstance dom lang)
    (tr : CSPTransferHypothesis M dom lang)
    (solver : PolyTimeCSPSolver dom lang) : False
```
- **File:** `CSPAlgebraLock.lean:106-118`
- **Axioms:** propext, Classical.choice, sideA_bounded_selector_impossible, Quot.sound

```lean
theorem chain4_regime_lock
    (M : GradedReflModel_Mirror) (hub : SelfAppUnbounded_Mirror M)
    (dom : CSPDomain) (lang : ConstraintLanguage dom)
    (rt : CSPRegimeTransfer M dom lang)
    (solver : PolyTimeCSPSolver dom lang) : False
```
- **File:** `CSPAlgebraLock.lean:208-217`
- **Axioms:** propext, Classical.choice, sideA_bounded_selector_impossible, Quot.sound
- **Hypotheses:** CSPRegimeTransfer (bundles CSPTransferHypothesis + PolymorphismFaithful + UnboundedPolymorphismRequirement) — MOOT via BridgeVacuity

**4. Bridge condition.**
- `CSPTransferHypothesis M dom lang` — Field: `transfer` mapping BoundedAlgebraicWitness to grade-bounded function agreeing with selfApp. MOOT (BridgeVacuity).
- `PolymorphismFaithful` — Fields: `depth_transfer` (depth distortion function), `depth_poly` (polynomial bound), `depth_bounded`. MOOT (BridgeVacuity).

**5. Bridge paths.** Both Path 1 and Path 2 (tractable case).

*Path 2 (direct bridge, tractable case only, no custom axioms):*
```lean
theorem chain4_csp_model_data_bridge
    (M : GradedReflModel_Mirror)
    (hub : SelfAppUnbounded_Mirror M)
    (cmd : CSPModelData M) : False
```
- **File:** `CSPDirectBridge.lean:165-169`
- **Axioms:** propext, Quot.sound (no custom axioms)
- **Hypotheses (Path 2):** CSPModelData M

*Path 2 bridge condition:*
- `CSPModelData M` — Fields: `red`, `red_grade_le`, `red_idempotent`, `selfApp_eq_red`. Same 4-field pattern as Chains 2, 3, 5.
- **Tractable case:** When WNU polymorphism exists, `wnu_model_data` constructs CSPModelData on the WNU-GRM (carrier = D, grade = const 0, selfApp = id by WNU idempotency). This is grade-trivial.
- **Hard case:** CSPModelData is uninhabitable (`csp_modeldata_uninhabitable_iff_hard`). The hard case requires CSPRegimeTransfer (Path 1).
- **Multi-sorted obstacle:** The clone algebra's arity-indexed structure cannot be encoded as a single fold/unfold pair on a non-trivial graded model. This is why the WNU-GRM is grade-trivial.

**6. Dependencies.** Imports: SideAMirror.lean (axiom), CookSelectorBridge.lean, CookFaithfulness.lean, Chain5_Algebraic.AlgebraicProofLock (for selfApp_nonincreasing_contradiction). No other cross-chain imports.

**7. Group placement.** Chain 4 has a direct bridge for the tractable case (WNU exists) via CSPModelData on the WNU-GRM. The hard case (no WNU) remains Path 1 only. Boolean CSP specialization (`no_poly_boolean_csp_solver`) demonstrates Chain 4 subsumes Chain 1 on Boolean domain.

---

### Chain 6 — Extension Complexity

**1. Chain identity.**
- **Domain:** Linear programming extensions, slack matrices, nonnegative rank, correlation polytopes.
- **Directory:** `ClassicalConstraints/Chain6_Extension/`
- **Files (7):**
  - `SATPolytopeCore.lean` — Polytope, SATPolytope, correlation polytope structures
  - `SlackMatrixCore.lean` — slackMatrix, NonnegFactorization, ExtendedFormulation, YannakakisTheorem
  - `NonnegRankObstruction.lean` — FoolingSet, fooling_set_lower_bound
  - `ExtensionSelectorBridge.lean` — GeometricFaithful, PolyLPSolver, lp_size_bounds_nonneg_rank
  - `ExtensionComplexityLock.lean` — Lock theorem, GeometricTransferHypothesis
  - `DirectBridgeAnalysis.lean` — ExtensionModelData (4-field), chain6_direct_bridge, GeometricModelDataObstruction (circularity analysis)
  - `BridgeVacuity.lean` — geometric_transfer_hypothesis_uninhabitable, BridgeVacuity for Chain 6

**2. Key structures.**

| Structure | File | Purpose | Source |
|-----------|------|---------|--------|
| `Polytope` | SATPolytopeCore.lean | Convex polytope (vertices + facets) | Chain-specific |
| `SATPolytope` | SATPolytopeCore.lean | Polytope associated with SAT instance | Chain-specific |
| `NonnegFactorization` | SlackMatrixCore.lean | Nonneg matrix factorization M = L * R | Chain-specific |
| `YannakakisTheorem` | SlackMatrixCore.lean | Extension complexity = nonneg rank | External result (structure) |
| `FoolingSet` | NonnegRankObstruction.lean | Fooling set for nonneg rank lower bound | Chain-specific |
| `GeometricFaithful` | ExtensionSelectorBridge.lean | Hard polytope family with superpolynomial nonneg rank | Chain-specific |
| `GeometricTransferHypothesis` | ExtensionComplexityLock.lean | BoundedSelector -> grade-bounded function on M | Chain-specific (moot: BridgeVacuity) |
| `ExtensionModelData` | DirectBridgeAnalysis.lean | red + grade-non-increasing + idempotent + selfApp_eq_red (4-field) | Chain-specific (formally proved but CANNOT be instantiated — circularity) |
| `GeometricModelDataObstruction` | DirectBridgeAnalysis.lean | Documents why ExtensionModelData cannot be constructed from geometric data | Chain-specific |

**3. Lock theorem.**
```lean
theorem no_poly_sat_solver_geometric
    (M : GradedReflModel_Mirror) (hub : SelfAppUnbounded_Mirror M)
    (family : SATFamily) (enc : CookEncoding) (cf : CookFaithful enc)
    (tr : GeometricTransferHypothesis M family enc cf)
    (solver : PolyTimeSolver family) : False
```
- **File:** `ExtensionComplexityLock.lean:104-119`
- **Axioms:** propext, sideA_bounded_selector_impossible
- **Bridge path:** Path 1 only
- **Hypotheses:** CookFaithful enc, GeometricTransferHypothesis (both MOOT via BridgeVacuity)

**4. Bridge condition.**
- `GeometricTransferHypothesis M family enc cf` — Field: `transfer` mapping BoundedSelector to grade-bounded function agreeing with selfApp. MOOT (BridgeVacuity).
- `CookFaithful enc` — shared with Chain 1. MOOT (BridgeVacuity).

**5. Bridge paths.** Path 1 and Path 2 (formal, with circularity caveat).

*Path 2 (direct bridge, formally proved, no custom axioms):*
```lean
theorem chain6_direct_bridge
    (M : GradedReflModel_Mirror)
    (hub : SelfAppUnbounded_Mirror M)
    (emd : ExtensionModelData M) : False
```
- **File:** `DirectBridgeAnalysis.lean:86-90`
- **Axioms:** propext, Quot.sound (no custom axioms)
- **Hypotheses (Path 2):** ExtensionModelData M

*Path 2 bridge condition:*
- `ExtensionModelData M` — Fields: `red`, `red_grade_le`, `red_idempotent`, `selfApp_eq_red`. Same 4-field pattern as other chains.
- **CIRCULARITY CAVEAT:** The theorem is proved, but ExtensionModelData CANNOT be instantiated from geometric data without circularity. Providing ExtensionModelData is equivalent to assuming selfApp is grade-bounded, which is the regime conclusion. `GeometricModelDataObstruction` documents this precisely.
- **Why:** Nonneg rank is combinatorial, not syntactic. No canonical nonneg-rank-reducing operation exists that equals selfApp. The Fiorini-Rothvoss-Tiwary lower bounds mean any rank-reducing map fundamentally changes the polytope.
- **GeometricTransferHypothesis** remains the correct open-hypothesis formulation for Chain 6.

**6. Dependencies.** Imports: SideAMirror.lean (axiom), CookSelectorBridge.lean, CookFaithfulness.lean. Mathlib (Matrix, Real). No imports from other chains.

**7. Group placement.** Group A (effectively). Chain 6 has a formally proved direct bridge theorem (`chain6_direct_bridge`), but ExtensionModelData cannot be constructed from geometric data without circularity. GeometricTransferHypothesis remains the correct open condition.

---

## Dependencies

All chains import from Shared/:
- `SideAMirror.lean` — 35 declarations (9 structures, 7 defs, 1 axiom, 18 theorems), includes GRM morphism framework, Lambek data, partial Lambek, RelevantSubdomain, GRMEndofunctor, bridge factory, `selfApp_nonincreasing_contradiction` (proved)
- `CookSelectorBridge.lean` — SATFamily, BoundedSelector, PolyTimeSolver, PolyBound, `poly_solver_induces_bounded_selector`
- `CookFaithfulness.lean` — CookEncoding, CookFaithful, ObstructionProfile
- `Basic.lean` — InstanceFamily
- `SATPresheafCore.lean` — SATInstance, presheaf gluing

Cross-chain imports: Chain 2 (`ProofComplexityPartialLambek.lean`) and
Chain 3 (`DescriptiveComplexityPartialLambek.lean`) both import
`Chain5_Algebraic.AlgebraicProofLock` to reuse the partial Lambek /
RelevantSubdomain infrastructure. All other cross-chain references go
through Shared/ only.

## Bridge Path Summary

| Chain | Group | Path 1 (Lock) | Path 2 (Direct) | Custom axioms | Path 2 notes |
|-------|-------|---------------|-----------------|---------------|--------------|
| 1 | -- | `no_poly_sat_solver` | `chain1_direct_bridge` | sideA (Path 1 only) | 2-field SATModelData; grade-non-increasing suffices |
| 2 | B | -- | `chain2_direct_bridge` | none | 4-field ProofComplexityModelData |
| 3 | B | `no_poly_sat_solver_descriptive` | `chain3_direct_bridge` | sideA (Path 1 only) | 4-field DescriptiveComplexityModelData |
| 4 | -- | `no_poly_csp_solver_via_transfer` | `chain4_csp_model_data_bridge` | sideA (Path 1 only) | Tractable case only (WNU exists); hard case Path 1 |
| 5 | B | `algebraic_proof_lock_via_transfer` | `chain5_direct_bridge` | sideA (Path 1 only) | 4-field AlgebraicModelData |
| 6 | A | `no_poly_sat_solver_geometric` | `chain6_direct_bridge` | sideA (Path 1 only) | Formally proved but CANNOT be instantiated (circularity) |
| 7 | C | `no_bounded_protocol_shortcuts` | `chain7_direct_bridge` | sideA (Path 1 only) | 4-field ProtocolModelData; DWS.project built-in |

Path 1 uses `sideA_bounded_selector_impossible` (custom axiom, proved in pnp-integrated).
Path 2 uses `selfApp_nonincreasing_contradiction` (proved theorem, propext + Quot.sound only).

## Direct bridge red operations (cross-chain pattern)

| Chain | red operation | Grade | Canonical fragment | Notes |
|-------|--------------|-------|--------------------|-------|
| 5 | multilinearReduce | totalDegree | multilinear polynomials | Group B, 4-field |
| 2 | dt_to_proto . proto_to_dt | depth | decision-tree protocols | Group B, 4-field |
| 3 | foCanonical (NNF) | quantifier rank | NNF formulas | Group B, 4-field |
| 1 | selfApp itself | grade | (none — selfApp is the reduction) | 2-field, no idempotence |
| 4 | WNU diagonal (tractable) | const 0 | D (domain values) | Tractable case only; grade-trivial |
| 7 | DWS.project | cost | projected states | Built-in idempotent + cost-reducing |
| 6 | (hypothetical face projection) | nonneg rank | (cannot be constructed) | Formally proved; circular to instantiate |

Group B (Chains 5, 2, 3): idempotent, grade-preserving, evaluation-preserving
projections. Each projects onto a canonical subdomain. Cofinality is
structural — any overflow witness projects to a canonical element with
same grade and same selfApp value. The shared obstruction to GRM
instantiation is the fold/unfold roundtrip: all three projections lose
structural information that no fold can recover.

Chain 1: minimal 2-field structure (grade-non-increasing selfApp only).
Chain 4: tractable case uses WNU-GRM (grade-trivial); hard case has no ModelData.
Chain 7: DWS.project is already idempotent and cost-reducing by construction.
Chain 6: formally proved but circularly dependent on the regime conclusion.
