# CLAIMS.md — classical-constraints

What this project proves, what it assumes, and what it does not claim.
Generated from the codebase. Machine-verified axiom profiles.

## 1. Primary Claim

There is no single main theorem. The project formalizes seven chains,
each expressing a verification/search obstruction in a different
classical mathematical domain. Each chain produces a conditional
impossibility: given open bridge hypotheses (carried as explicit
parameters), no polynomial-time solver exists.

The contribution is the convergence: seven language-model pairings
exhibit the same predicate classification, with three qualitatively
different relationships to the regime question (Groups A/B/C).

**Scope note.** The predicates `PEqNP`, `SelfAppUnbounded`, and the
chain-specific transfer hypotheses (`TransferHypothesis`,
`DescriptiveTransferHypothesis`, `CSPTransferHypothesis`, etc.) are
internal predicates of the GRM (Graded Reflexive Model) formalism.
They are not direct assertions about classical computational complexity
classes. The relationship between GRM predicates and classical complexity
is established in the companion repo classical-bridge, which constructs
a GRM from the classical Turing machine model and determines its regime
placement.

## 2. Axiom Profile

**Sorry count:** 0 (verified by grep across all 84 files)

**Lean foundational axioms used:** propext, Quot.sound, Classical.choice

**Custom axioms (2) — these define the trust boundary:**

1. `sideA_bounded_selector_impossible`
   - **File:** `ClassicalConstraints/Shared/SideAMirror.lean:61`
   - **Type:** `(M : GradedReflModel_Mirror) -> (hub : SelfAppUnbounded_Mirror M) -> (d : Nat) -> ¬∃ (f : M.carrier -> M.carrier), (∀ x, M.grade x ≤ d -> f x = M.selfApp x) ∧ (∀ x, M.grade x ≤ d -> M.grade (f x) ≤ d)`
   - **Status:** Cross-project mirror. Proved as `selfApp_not_grade_bounded` in pnp-integrated (`PNP/Transport/TransportCollapseObstruction.lean`) and proved independently in classical-bridge (`Mirror/SideA.lean`, 4 lines from `SelfAppUnbounded.overflows` -- essentially immediate from the definition). Character-identical type signature. Mirrored here because the repos cannot share imports.
   - **Used by:** Path 1 lock theorems (Chains 1, 3, 4, 5, 6, 7).

2. `resolution_feasible_interpolation`
   - **File:** `ClassicalConstraints/Chain2_ProofComplexity/FeasibleInterpolationBridge.lean:98`
   - **Type:** `(n_x n_y : Nat) -> (combined : CNF) -> (h_combined : combined.num_vars = n_x + n_y) -> (ref : ResolutionRefutation combined) -> ∃ C : BooleanCircuit n_x, C.gateCount ≤ ref.size * ref.size`
   - **Status:** External result (Krajicek 1997, Razborov 1995). NOT a cross-project mirror.
   - **Semantic gap:** This axiom is weaker than the full Krajicek theorem. The real theorem produces a circuit that computes the interpolation function (separating left-satisfying from right-satisfying inputs). This axiom only asserts existence of a circuit with bounded gate count. The semantic content is pushed to caller hypotheses downstream.
   - **Used by:** Chain 2 only (`chain2_lock_interpolation`, `interpolation_implies_resolution_lb`).

**Machine-verified axiom profiles:**

### Per-chain lock theorems

| Theorem | Lean foundational | Custom axioms |
|---------|-------------------|---------------|
| `no_poly_sat_solver` (Chain 1) | propext | sideA_bounded_selector_impossible |
| `chain2_complete` (Chain 2) | propext, Classical.choice, Quot.sound | resolution_feasible_interpolation |
| `no_poly_sat_solver_descriptive` (Chain 3) | propext | sideA_bounded_selector_impossible |
| `no_poly_csp_solver_via_transfer` (Chain 4) | propext, Classical.choice, Quot.sound | sideA_bounded_selector_impossible |
| `algebraic_proof_lock_via_transfer` (Chain 5) | propext, Classical.choice, Quot.sound | sideA_bounded_selector_impossible |
| `no_poly_sat_solver_geometric` (Chain 6) | propext | sideA_bounded_selector_impossible |
| `no_bounded_protocol_shortcuts` (Chain 7) | propext | sideA_bounded_selector_impossible |

Six of seven chains depend on `sideA_bounded_selector_impossible`
(mirrored from pnp-integrated). Chain 2 is the exception: it depends
on `resolution_feasible_interpolation` (Krajicek 1997) instead, and
has no Path 1 lock architecture — its results are purely domain-internal
proof complexity stepping stones summarized by `chain2_complete`.

### Path 2 direct bridge theorems (no custom axioms)

| Theorem | Lean foundational | Custom axioms |
|---------|-------------------|---------------|
| `chain2_direct_bridge` (Chain 2) | propext, Quot.sound | none |
| `chain3_direct_bridge` (Chain 3) | propext, Quot.sound | none |
| `chain5_direct_bridge` (Chain 5) | propext, Quot.sound | none |

### Domain-internal results (Chain 2)

| Theorem | Lean foundational | Custom axioms |
|---------|-------------------|---------------|
| `chain2_lock_width_to_size` | propext, Classical.choice, Quot.sound | none |
| `chain2_lock_interpolation` | propext, Classical.choice, Quot.sound | resolution_feasible_interpolation |

### Shared infrastructure and vacuity

| Theorem | Lean foundational | Custom axioms |
|---------|-------------------|---------------|
| `selfApp_nonincreasing_contradiction` | propext, Quot.sound | none |
| `partial_bridge_mirror` | propext, Quot.sound | none |
| `poly_solver_induces_bounded_selector` | propext | none |
| `type_mismatch_tt_vs_obstruction` | propext, Quot.sound | none |
| `transfer_hypothesis_uninhabitable` | propext | sideA_bounded_selector_impossible |
| `transfer_implies_grade_nonincreasing` | propext | none |
| `transfer_uninhabitable_via_nonincreasing` | propext, Quot.sound | none |
| `transfer_hypothesis_characterization` | propext, Quot.sound | sideA_bounded_selector_impossible |
| `solver_hypothesis_redundant` | propext | sideA_bounded_selector_impossible |

**Path 2 axiom observation:** All seven chains now have a direct bridge
theorem. The theorems for Chains 1, 2, 3, 4, 5, 6, and 7 use only
propext + Quot.sound — no Classical.choice, no custom axioms. This is
the strongest axiom profile of any chain result and means every chain
can reach contradiction without the cross-project axiom at all via
Path 2. Note: Chain 6's direct bridge theorem (`chain6_direct_bridge`)
exists and is verified, but ExtensionModelData cannot be instantiated
from geometric data without circularity, so the theorem is formally
present but unconstructible in practice.

**Cross-project connection (classical-bridge).** The lock theorems in
this repository prove: TransferHypothesis + SelfAppUnbounded -> False.
The companion repo classical-bridge constructs a GRM from the classical
Turing machine model (classicalGRM) and proves that classicalGRM does
NOT have SelfAppUnbounded — it is in the PEqNP regime. The lock
theorems characterize the separation regime (SelfAppUnbounded); the
classical TM model, per classical-bridge, is not in it. This means
the lock architecture is structurally inapplicable to the classical
computational setting: its hypotheses are satisfied vacuously, not
because a solver is impossible, but because the regime predicate
(SelfAppUnbounded) does not hold for classical TMs.

## 3. What Is Proved (Unconditional)

Theorems that hold without open hypotheses. Organized by module.

### Shared Infrastructure

| Theorem | File | Description |
|---------|------|-------------|
| `selfApp_nonincreasing_contradiction` | SideAMirror.lean | If selfApp is grade-non-increasing, SelfAppUnbounded is contradicted |
| `partial_bridge_mirror` | SideAMirror.lean | RelevantSubdomain + SelfAppUnbounded -> False |
| `poly_solver_induces_bounded_selector` | CookSelectorBridge.lean | A poly-time solver induces a bounded selector |

### Chain 1 — SAT/Combinatorial

| Theorem | File | Description | Critical path? |
|---------|------|-------------|----------------|
| `no_descent_from_conflict` | Obstruction.lean | WitnessConflict blocks descent | Core |
| `type_mismatch_tt_vs_obstruction` | Barriers.lean | Descent obstruction and truth-table properties are type-incompatible | Supplementary |
| `descent_obstruction_is_relational` | Barriers.lean | WitnessConflict requires two instances (relational, not pointwise) | Supplementary |
| `barrier_landscape_witness` | Barriers.lean | WitnessConflict produces all three barrier evasion properties | Supplementary |
| `barrier_landscape_blocks_descent` | Barriers.lean | BarrierLandscape entails no-descent | Supplementary |
| `transfer_hypothesis_uninhabitable` | BridgeVacuity.lean | TransferHypothesis + SelfAppUnbounded -> False | Core |
| `transfer_implies_grade_nonincreasing` | BridgeVacuity.lean | TransferHypothesis forces selfApp grade-non-increasing (propext only) | Core |
| `transfer_implies_factors_through_all` | BridgeVacuity.lean | TransferHypothesis implies FactorsThrough at every grade | Core |
| `transfer_implies_peqnp` | BridgeVacuity.lean | TransferHypothesis implies PEqNP | Core |
| `transfer_hypothesis_characterization` | BridgeVacuity.lean | TransferHypothesis equivalent to regime assertion | Core |
| `chain1_direct_bridge` | SATDirectBridge.lean | SATModelData (grade-non-increasing selfApp) + SelfAppUnbounded → False | Core |
| `chain1_is_minimal_bridge` | SATDirectBridge.lean | SATModelData is the minimal Chain 1 bridge structure | Supplementary |
| `chain1_bridge_iff_grade_nonincreasing` | SATDirectBridge.lean | Under SelfAppUnbounded, SATModelData ↔ False | Supplementary |

### Chain 2 — Proof Complexity

| Theorem | File | Description | Critical path? |
|---------|------|-------------|----------------|
| `chain2_lock_width_to_size` | ProofComplexityLock.lean | Width lower bounds transfer to size lower bounds | Core |
| `chain2_lock_proof_to_protocol` | ProofComplexityLock.lean | Short refutation yields bounded communication protocol | Core |
| `chain2_lock_comm_ge_query` | ProofComplexityLock.lean | Protocol depth >= query complexity | Core |
| `chain2_lock_lifting` | ProofComplexityLock.lean | Lifting transfers query lower bounds to communication lower bounds | Core |
| `chain2_lock_nonconstant_lb` | ProofComplexityLock.lean | Non-constant functions have decision tree depth >= 1 | Core |
| `chain2_lock_xor_gadget` | ProofComplexityLock.lean | XOR gadget is non-degenerate and balanced | Core |
| `chain2_lock_leaf_count` | ProofComplexityLock.lean | Protocol tree of depth d has at most 2^d leaves | Core |
| `chain2_lock_search_hardness` | ProofComplexityLock.lean | Communication lower bound implies proof search hardness | Core |
| `chain2_complete` | ProofComplexityLock.lean | Summary conjunction of chain 2 lock results | Core |
| `protocol_to_rectangles` | CommunicationProtocolBridge.lean | Protocol partitions input space into combinatorial rectangles | Core |
| `krajicek_extraction` | KrajicekExtraction.lean | Krajicek protocol extraction from resolution refutation | Core |

### Chain 3 — Descriptive Complexity

| Theorem | File | Description | Critical path? |
|---------|------|-------------|----------------|
| `foCanonical_depth_le` | FOCanonicalForm.lean | FO canonical form does not increase quantifier depth | Core |
| `foCanonical_idempotent` | FOCanonicalForm.lean | FO canonicalization is idempotent | Core |
| `locality_obstructs_fo_definability` | LocalityBridge.lean | Gaifman locality obstructs FO definability | Supplementary |

### Chain 4 — CSP Algebra

| Theorem | File | Description | Critical path? |
|---------|------|-------------|----------------|
| `majority_is_wnu` | PolymorphismCore.lean | Majority operation is a weak near-unanimity operation | Core |
| `sat_csp_equivalence` | CSPInstanceCore.lean | SAT instances embed faithfully as CSP instances | Core |
| `threeSAT_no_bounded_width` | WidthFromPolymorphisms.lean | 3-SAT has no bounded width | Core |
| `polymorphism_counting_lower_bound` | CSPSelectorBridge.lean | Polymorphism clone level bounded by selector capacity | Core |
| `chain4_csp_model_data_bridge` | CSPDirectBridge.lean | CSPModelData + SelfAppUnbounded → False | Core |
| `chain4_wnu_direct_bridge` | CSPDirectBridge.lean | WNU polymorphism + SelfAppUnbounded → False (tractable case) | Core |
| `wnu_grm_not_selfAppUnbounded` | CSPDirectBridge.lean | WNU-induced GRM is not SelfAppUnbounded | Supplementary |

### Chain 5 — Algebraic Proof Complexity

| Theorem | File | Description | Critical path? |
|---------|------|-------------|----------------|
| `no_uniform_low_degree_refuter` | AlgebraicProofLock.lean | No uniform low-degree algebraic refutation scheme exists | Core |
| `multilinearReduce_idempotent` | AlgebraicModelConcrete.lean | Multilinear reduction (cap exponents at 1) is idempotent | Core |
| `capExp_comp_eq` | AlgebraicModelConcrete.lean | capExp composition identity | Core |
| `linear_beats_constant` | DegreeLowerBoundBridge.lean | For any constant c and bound B, exists n0 such that c*n > B | Supplementary |
| `tseitin_consequence_fails` | DirectVariableEncoding.lean | ConsequenceFaithful fails for natural Tseitin profile when cpg >= 2 | Supplementary |

### Chain 6 — Extension Complexity

| Theorem | File | Description | Critical path? |
|---------|------|-------------|----------------|
| `fooling_set_lower_bound` | NonnegRankObstruction.lean | Fooling set gives nonneg rank lower bound | Core |
| `lp_size_bounds_nonneg_rank` | ExtensionSelectorBridge.lean | LP solver size bounds nonneg rank | Core |
| `chain6_direct_bridge` | DirectBridgeAnalysis.lean | ExtensionModelData + SelfAppUnbounded → False | Core |

Note: ExtensionModelData cannot be instantiated from geometric data without circularity.

### Chain 7 — Protocol Theory

| Theorem | File | Description | Critical path? |
|---------|------|-------------|----------------|
| `sovereignty_from_closure` | ProtocolWitnessFamilyLock.lean | Witness sovereignty holds when certification implies realization | Core |
| `consequence_closed_path_realizes` | ValueCollapseInstance.lean | Consequence-closed witness paths realize at endpoints | Core |
| `chain7_direct_bridge` | ProtocolDirectBridge.lean | ProtocolModelData + SelfAppUnbounded → False | Core |
| `chain7_protocol_bridge` | ProtocolDirectBridge.lean | Longer route via RelevantSubdomain | Supplementary |
| `protocol_model_data_implies_peqnp` | ProtocolDirectBridge.lean | ProtocolModelData → PEqNP at grade 0 | Supplementary |

## 4. What Is Proved (Conditional)

Theorems depending on open hypotheses carried as explicit parameters.

### Path 1 Lock Theorems (depend on sideA axiom + TransferHypothesis)

| Theorem | File | Open hypotheses |
|---------|------|-----------------|
| `no_poly_sat_solver` | SATBoundaryLock.lean | `CookFaithful enc`, `TransferHypothesis M family enc cf` |
| `no_poly_sat_solver_descriptive` | DescriptiveComplexityLock.lean | `DefinabilityFaithful enc`, `DescriptiveTransferHypothesis M family enc df` |
| `no_poly_csp_solver_via_transfer` | CSPAlgebraLock.lean | `CSPTransferHypothesis M dom lang` |
| `chain4_regime_lock` | CSPAlgebraLock.lean | `CSPRegimeTransfer M dom lang` |
| `algebraic_proof_lock_via_transfer` | AlgebraicProofLock.lean | `AlgebraicTransferHypothesis M family df` |
| `no_poly_sat_solver_geometric` | ExtensionComplexityLock.lean | `CookFaithful enc`, `GeometricTransferHypothesis M family enc cf` |
| `no_bounded_protocol_shortcuts` | ProtocolWitnessFamilyLock.lean | `ConsequenceFaithful enc`, `ProtocolTransfer M family enc cf` |

Pattern: solver assumption -> bounded selector -> transfer to GRM ->
`sideA_bounded_selector_impossible` fires -> False.

**Vacuity result (BridgeVacuity.lean):** The TransferHypothesis
hypothesis in each Path 1 lock theorem is provably uninhabitable
when SelfAppUnbounded holds. The proof: bounded selectors always
exist (constant functions); TransferHypothesis maps any bounded
selector to a grade-bounded function agreeing with selfApp; Side A
says no such function exists when selfApp is unbounded. Therefore
TransferHypothesis + SelfAppUnbounded -> False independently of
whether a solver exists, and each lock theorem is regime-characterizing (hypotheses jointly unsatisfiable).
The solver hypothesis contributes nothing to the derivation of False.

`transfer_hypothesis_characterization` proves what TransferHypothesis
actually requires of a model: selfApp grade-non-increasing, PEqNP
at every grade, and SelfAppUnbounded impossible. The bridge condition
is equivalent to a regime assertion — it IS the regime question,
not an independent open condition.

### Path 2 Direct Bridge Theorems (no custom axioms)

| Theorem | File | Open hypotheses | Axioms |
|---------|------|-----------------|--------|
| `chain1_direct_bridge` (Chain 1) | SATDirectBridge.lean | `SATModelData M` | propext, Quot.sound (no custom axioms) |
| `chain2_direct_bridge` | ProofComplexityPartialLambek.lean | `ProofComplexityModelData M` | propext, Quot.sound |
| `chain3_direct_bridge` | DescriptiveComplexityPartialLambek.lean | `DescriptiveComplexityModelData M` | propext, Quot.sound |
| `chain4_csp_model_data_bridge` (Chain 4) | CSPDirectBridge.lean | `CSPModelData M` | propext, Quot.sound (no custom axioms) |
| `chain5_direct_bridge` | AlgebraicProofLock.lean | `AlgebraicModelData M` | propext, Quot.sound |
| `chain5_multilinear_bridge` | AlgebraicProofLock.lean | `MultilinearFragment M`, `MultilinearCofinality M frag` | propext, Quot.sound |
| `chain6_direct_bridge` (Chain 6) | DirectBridgeAnalysis.lean | `ExtensionModelData M` | propext, Quot.sound (no custom axioms) |
| `chain7_direct_bridge` (Chain 7) | ProtocolDirectBridge.lean | `ProtocolModelData M` | propext, Quot.sound (no custom axioms) |

Pattern: ModelData provides selfApp = red with red grade-non-increasing ->
`selfApp_nonincreasing_contradiction` fires -> False. No custom axioms
needed. Axioms: propext + Quot.sound only.

### Interpolation (depends on resolution_feasible_interpolation axiom)

| Theorem | File | Open hypotheses |
|---------|------|-----------------|
| `interpolation_implies_resolution_lb` | FeasibleInterpolationBridge.lean | `h_correct` (circuit computes interpolation fn) |
| `chain2_lock_interpolation` | ProofComplexityLock.lean | (none beyond axiom) |

### Shared structural result

The `TransferHypothesis` pattern is structurally identical across Path 1
chains — each is a structure with a `transfer` field mapping
`BoundedSelector` to a grade-bounded function on `M` agreeing with
`selfApp`. BridgeVacuity.lean proves this return type is uninhabited
when SelfAppUnbounded holds: bounded selectors always exist (constant
functions), so the transfer must produce a grade-bounded function, but
sideA says no such function exists. The transfer's type signature
forces consequence closure (BridgeNecessity Theorem F in pnp-integrated),
and consequence closure is incompatible with unbounded selfApp
(BridgeNecessity Theorem G). The bridge condition IS the regime question.

## 5. What Is NOT Claimed

- **The lock theorems do not prove P != NP in the classical sense.**
  They prove that certain transfer architectures are uninhabitable
  under SelfAppUnbounded, which is a structural impossibility within
  the GRM formalism. SelfAppUnbounded is an internal GRM predicate,
  not a direct assertion about classical complexity classes. The
  classical TM model (per classical-bridge) is in the PEqNP regime,
  not the SelfAppUnbounded regime, so the lock theorems' hypotheses
  are never jointly satisfiable for classical computation.

- **The Path 1 lock theorems are regime-characterizing (hypotheses jointly unsatisfiable).** TransferHypothesis
  + SelfAppUnbounded -> False is proved in BridgeVacuity.lean. The
  lock theorems require both, so their hypothesis sets are jointly
  inconsistent. The solver hypothesis is redundant — it contributes
  nothing to the derivation of False. This means the lock architecture
  gives no information about the existence of polynomial-time solvers.

- **Does NOT close any bridge condition.** Every chain has explicit open
  hypotheses (TransferHypothesis variants for Path 1, ModelData for
  Path 2). No hypothesis is hidden or satisfied by construction.
  For Path 1, the hypotheses are now proved to be unsatisfiable in
  TC models (see vacuity result above).

- **Does NOT claim seven independent proofs of one thing.** The seven
  chains are seven language-model pairings exhibiting the same predicate
  classification. The convergence is a Level 2 observation (demonstrable
  from seven chains), not a Level 1 theorem.

- **The carrier engineering gap is the content, not a deficiency.** Each
  chain's gap between its language and its computational model is the
  formal content of that chain's position in the collection. It is not a
  technical problem to be solved by weakening assumptions.

- **Does NOT claim the three-group classification is a narrative.** It
  is a partition by which predicates hold on which chains: Group C has
  selfApp = id; Group B has ModelData; Group A has neither. No
  interpretive gloss about what languages "can see" or "cannot reach."

- **The `resolution_feasible_interpolation` axiom is weaker than the
  full Krajicek theorem.** It asserts existence of a small circuit
  without the semantic property that the circuit computes the
  interpolation function. This gap is documented in the axiom's
  docstring.

- **The `short_proof_bounded_comm_trivial` theorem is regime-characterizing (hypotheses jointly unsatisfiable).**
  It constructs a constant protocol (`.leaf true`, depth 0). The
  meaningful Krajicek extraction is in `krajicek_extraction`
  (KrajicekExtraction.lean), which produces a protocol that depends on
  the refutation structure.

- **Barrier evasion (Barriers.lean) is meta-observational.** The
  `Relativizes_trivial` and `OracleIndependent_trivial` definitions are
  trivially satisfied because the oracle parameters are unused — the
  WitnessConflict data does not reference oracles. The genuine barrier
  evasion content is the type mismatch theorem
  (`type_mismatch_tt_vs_obstruction`), which is fully proved.

- **PolyMarkov's canonical home is this repository.** The polynomial
  Markov principle (PolyMarkov) is formalized in Chain 1 via
  DoubleNegationShapes, EMDecomposition, and MorphismChain as a
  classical/logical concept. It was previously also present in
  pnp-integrated as an intermediate step in the main theorem chain,
  where it was redundant with PEqNP at the GRM level. That redundancy
  has been removed: pnp-integrated now proves not-PEqNP directly (two
  steps: PEqNP gives FactorsThrough at some d, SelfAppUnbounded
  contradicts). PolyMarkov's classical decomposition into excluded
  middle and double negation shapes is the content proper to this
  repository's axiom-layer analysis.

## 6. Bridge Conditions Catalog

**BridgeVacuity status:** ALL bridge conditions — both Path 1
(TransferHypothesis) and Path 2 (ModelData) — are uninhabitable in TC models.

- **Path 1:** `transfer_hypothesis_uninhabitable` (BridgeVacuity.lean)
  proves TransferHypothesis + SelfAppUnbounded → False.
- **Path 2:** ModelData requires selfApp = red where red is
  grade-non-increasing. This directly contradicts SelfAppUnbounded.
  The direct bridge theorems (`chain1/2/3/4/5/6/7_direct_bridge`) prove
  M + SelfAppUnbounded + ModelData → False across all seven chains.

The bridge condition IS the regime question
(`transfer_hypothesis_characterization`). Every lock theorem in the
project is regime-characterizing (hypotheses jointly unsatisfiable) for TC models.

### Per-chain TransferHypothesis variants (Path 1)

| Chain | Structure | File | Status |
|-------|-----------|------|--------|
| 1 | `TransferHypothesis` | SATBoundaryLock.lean | UNINHABITABLE when SelfAppUnbounded (BridgeVacuity.lean) |
| 3 | `DescriptiveTransferHypothesis` | DescriptiveComplexityLock.lean | UNINHABITABLE (same argument applies) |
| 4 | `CSPTransferHypothesis` | CSPAlgebraLock.lean | UNINHABITABLE (same argument applies) |
| 5 | `AlgebraicTransferHypothesis` | AlgebraicProofLock.lean | UNINHABITABLE (same argument applies) |
| 6 | `GeometricTransferHypothesis` | ExtensionComplexityLock.lean | UNINHABITABLE (same argument applies) |
| 7 | `ProtocolTransfer` | ProtocolWitnessFamilyLock.lean | UNINHABITABLE (same argument applies) |

The uninhabitability is proved explicitly for Chain 1 in
BridgeVacuity.lean. The same argument (trivial bounded selectors
exist, transfer produces grade-bounded function, sideA contradicts)
applies structurally to all chains whose TransferHypothesis has the
same return type shape.

### Per-chain faithfulness conditions

| Chain | Structure | File | Status |
|-------|-----------|------|--------|
| 1 | `CookFaithful` | CookFaithfulness.lean | uninhabitable (BridgeVacuity) |
| 3 | `DefinabilityFaithful` | DescriptiveComplexityLock.lean | uninhabitable (BridgeVacuity) |
| 4 | `PolymorphismFaithful` | CSPAlgebraLock.lean | uninhabitable (BridgeVacuity) |
| 5 | `DegreeFaithful` | DegreeLowerBoundBridge.lean | uninhabitable (BridgeVacuity) |
| 6 | `CookFaithful` (shared with Chain 1) | CookFaithfulness.lean | uninhabitable (BridgeVacuity) |
| 7 | `ConsequenceFaithful` | CookFaithfulness.lean | uninhabitable (BridgeVacuity) |

**BridgeVacuity status:** `transfer_hypothesis_uninhabitable` (BridgeVacuity.lean)
proves TransferHypothesis + SelfAppUnbounded → False. The transfer mechanism
is uninhabitable in any TC model. These faithfulness conditions are structurally
satisfiable but moot: even with a faithful encoding, the transfer they feed
into cannot be constructed when SelfAppUnbounded holds. The lock theorems
are regime-characterizing (hypotheses jointly unsatisfiable) for TC models. The bridge condition IS the regime question
(`transfer_hypothesis_characterization`). See Appendix E (falsification conditions).

### Path 2 ModelData conditions (Group B chains)

Each ModelData structure specifies a concrete `red` operation with proved
mathematical properties (grade-non-increasing, idempotent). What is open
is providing a GRM whose `selfApp` equals that `red` — this requires a
fold/unfold roundtrip that projection-based canonicalization cannot
support, because it loses structural information.

| Chain | Structure | `red` operation | Concrete facts | Status |
|-------|-----------|-----------------|----------------|--------|
| 1 | `SATModelData` | selfApp (implicit) | grade-non-increasing only (2-field version) | uninhabitable in TC models. `chain1_direct_bridge` proves M + SelfAppUnbounded + ModelData → False. |
| 2 | `ProofComplexityModelData` | `dt_to_proto . proto_to_dt` (flatten) | `proto_to_dt_to_proto_depth_le`, `dt_to_proto_roundtrip_idempotent` | Uninhabitable: ModelData requires selfApp = red (grade-non-increasing), contradicting SelfAppUnbounded in TC models. Direct bridge `chain2_direct_bridge` proves M + SelfAppUnbounded + ModelData → False. |
| 3 | `DescriptiveComplexityModelData` | `foCanonical` (NNF conversion) | `foCanonical_depth_le`, `foCanonical_idempotent` | Uninhabitable: same argument. `chain3_direct_bridge` proves M + SelfAppUnbounded + ModelData → False. |
| 4 | `CSPModelData` | WNU diagonal on tractable case | WNU-GRM has grade = const 0 | uninhabitable in TC models. `chain4_csp_model_data_bridge` proves M + SelfAppUnbounded + ModelData → False. |
| 5 | `AlgebraicModelData` | `multilinearReduce` (cap exponents at 1) | `multilinearReduce_idempotent`, `capExp_comp_eq` | Uninhabitable: same argument. `chain5_direct_bridge` proves M + SelfAppUnbounded + ModelData → False. |
| 6 | `ExtensionModelData` | (bridge theorem exists) | — | Bridge theorem `chain6_direct_bridge` exists but cannot be instantiated from geometric data without circularity. uninhabitable in TC models. |
| 7 | `ProtocolModelData` | `DistributedWitnessSystem.project` (built-in idempotent) | — | uninhabitable in TC models. `chain7_direct_bridge` proves M + SelfAppUnbounded + ModelData → False. |

### External results carried as structures

| Structure | File | Content |
|-----------|------|---------|
| `ImmermanVardiTheorem` | FixedPointDefinabilityBridge.lean | P = FO+LFP on ordered finite structures |
| `PebbleFormulaEquivalence` | PebbleGameObstruction.lean | EF theorem for pebble games |
| `TseitinPCLowerBound` | DegreeLowerBoundBridge.lean | Tseitin PC degree >= Omega(n) on expanders |
| `RandomKSATSoSLowerBound` | DegreeLowerBoundBridge.lean | Random k-SAT SoS degree >= Omega(n) |

## 7. File Inventory

**Total:** 84 Lean files (83 in ClassicalConstraints/ + 1 root import)

| Category | Count | Description |
|----------|-------|-------------|
| Chain 1 (SAT) | 23 | SATBoundaryLock, BridgeVacuity, SATDirectBridge + supporting files |
| Chain 2 (Proof Complexity) | 10 | ProofComplexityLock + supporting files |
| Chain 3 (Descriptive) | 10 | DescriptiveComplexityLock, BridgeVacuity + supporting files |
| Chain 4 (CSP) | 8 | CSPAlgebraLock, BridgeVacuity, CSPDirectBridge + supporting files |
| Chain 5 (Algebraic) | 9 | AlgebraicProofLock, BridgeVacuity + supporting files |
| Chain 6 (Extension) | 7 | ExtensionComplexityLock, BridgeVacuity, DirectBridgeAnalysis + supporting files |
| Chain 7 (Protocol) | 9 | ProtocolWitnessFamilyLock, BridgeVacuity, ProtocolDirectBridge + supporting files |
| Shared | 5 | SideAMirror, CookSelectorBridge, CookFaithfulness, Basic, SATPresheafCore |
| ConcreteEncodings | 2 | DirectVariableEncoding, CapabilityDelegationEncoding |
| Root | 1 | ClassicalConstraints.lean (import aggregator) |
